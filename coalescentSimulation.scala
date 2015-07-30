/* [INDEX]

Overview......................................................................24
Usage.........................................................................46
Giry-Monad as `Distribution` trait............................................99
Stochastic processes and Markov chains.......................................481
Statistics...................................................................591
Partitions...................................................................629
Random populations...........................................................667
Random pedigrees.............................................................778
Coalescents in random pedigrees..............................................954
States and holding times representation.....................................1102
Meme model..................................................................1166
'Swedish families' model....................................................1197
Polygynous fish model.......................................................1243
Alien-ants model............................................................1319
Code formatting.............................................................1412
Parameter parsing...........................................................1475
Entry point, running the experiment.........................................1688

[/INDEX] */

/* #############################################################################
   [!]                              Overview
   ###########################################################################*/

// This software can be used to simulate random coalescents in fixed pedigrees.

// 
// The script is organized as follows: 
// - First, we define some general data structures that are helpful for dealing
//   with distributions and stochastic processes
// - Then we define a generic model of coalescent in random environment, 
//   with the underlying model of Mendelian randomness left abstract
// - We proceed by defining four concrete family structures
// - Then there are some facilities for generating help and formatting code 
// - Finally, the parameters are parsed, and the requested experiments are run

/*
 *
 * @author Andrey Tyukin
 * @date 2015-06
 */

/* #############################################################################
   [!]                               Usage
   ###########################################################################*/

/*
 * We wanted to minimize the effort that is necessary to get this software
 * running, and we did so by cramming everything into a single stand-alone 
 * script and avoiding any dependencies.
 *
 * This is a stand-alone script that can be executed with the 
 * Scala-interpreter. Assuming that you have Unix/Linux-like environment
 * with a Scala-interpreter, 
 * all you have to do is to `cd` into the directory that contains the script, 
 * and issue the following command:
 * {{{
 *    scala coalescentSimulation.scala --help
 * }}}
 * This will display the list of available options and show what a typical 
 * call to this software might look like.
 * 
 * Here is how one can launch simulations:
 * {{{
 *    scala coalescentSimulation.scala \
 *      -p 50 -N 100 --num-families-variation 0.8 --model 'Fish(2,5)' \
 *      -c 10000 -n 2 --exp-1-cdf --mrca-ecdf --track-progress --verbose
 * }}}
 * The above options mean: simulate 50 different pedigrees with 20-180 
 * fish-families with 2-5 females per family in each generation;
 * On each pedigree, simulate 10000 coalescents per pedigree with sample size 2
 * and print the emprical ECDF for each pedigree in the end. Show CDF of Exp_1
 * for comparison. Track progress, add experiment description to output.
 *
 * Less typical application might look as follows:
 * {{{
 *   scala coalescentSimulation.scala \
 *     -p 1 -N 1000 --num-families-variation 0.9 --model Meme \
 *     --only-populations --verbose
 * }}}
 * This would shown only population development, plotted against intrinsic time.
 *
 * In case you happen to run out of memory, you have to pass an option to the
 * JVM used by Scala:
 * {{{
 *   scala -J-Xmx2048m coalescentSimulation <optionsAsPreviously>
 * }}}
 */

import scala.math._
import scala.util.Random
import scala.collection.immutable.{Vector}
import scala.reflect.ClassTag 


/*##############################################################################
  [!]                 Giry-Monad as `Distribution` trait
  ############################################################################*/

/** 
 * Implementation of the Giry-monad.
 */
trait Distribution[X] { outer =>
  /** Generates a random realization */
  def sample: X

  /** Integrates real-valued function `f` exactly */
  def integral(f: X => Double): Double

  /** Integrates a real-valued function `f` approximately */
  def approxIntegral(f: X => Double, reps: Int = 1000): Double = {
    // the default implementation is a very simple Monte-Carlo method
    var sum = 0d
    var i = 0
    while (i < reps) { 
      sum += f(sample)
      i += 1
    }
    sum / reps
  }

  import Distribution.charFct // defined further below

  /** Computes probability of an event,
   * this is just integration of characteristic function 
   */
  def prob(event: X => Boolean): Double = integral(charFct(event))
  
  def approxProb(event: X => Boolean): Double = integral(charFct(event))

  /** Pushforward probability measure */
  def map[Y](f: X => Y): Distribution[Y] = new Distribution[Y] {
    def sample = f(outer.sample)
    def integral(g: Y => Double) = outer.integral{ x => g(f(x)) }
  }
  /** Multiple step random experiment */
  def flatMap[Y](markovKernel: X => Distribution[Y]): Distribution[Y] = 
  new Distribution[Y] {
    def sample = markovKernel(outer.sample).sample
    def integral(f: Y => Double) = outer.integral{
      x => markovKernel(x).integral(f) 
    }
  }
  /** Product with some other, `Y`-valued distribution */
  def zip[Y](other: Distribution[Y]): Distribution[(X,Y)] = 
  new Distribution[(X,Y)] {
    def sample = (outer.sample, other.sample)
    // Fubini
    def integral(f: ((X, Y)) => Double) = outer.integral{
      x => other.integral{ y => f((x, y)) }
    }
  }
  /** `n`-fold product with itself */
  def pow(n: Int): Distribution[Vector[X]] = new Distribution[Vector[X]] {
    def sample = {
      (for (i <- 1 to n) yield outer.sample).toVector
    }
    def integral(f: Vector[X] => Double) = {
      // Iterated fubini
      def integratePartiallyApplied(
        dim: Int, pa: Vector[X] => Double
      ): Double = {
        if (dim == 0) {
          // all arguments are already plugged in, 
          // `pa` is a function that takes empty vector and returns a constant
          pa(Vector())
        } else {
          // plug in one more variable, compute inner integral
          outer.integral{ 
            (x: X) => integratePartiallyApplied(dim - 1, {v => pa(v :+ x)})
          }
        }
      }
      integratePartiallyApplied(n, f)
    }
  }

  /** Infinite repetition of the same experiment */
  def repeat: StochasticProcess[X] = new StochasticProcess[X] {
    def sample: Stream[X] = outer.sample #:: sample
    /** 
     * Strangely enough, this actually works, but only as long as
     * `f` is guaranteed to look only at finitely many values. 
     * If it looks only "almost surely" at finitely many values, the 
     * method does not terminate.
     */
    def integral(f: Stream[X] => Double): Double = {
      (for {
        head <- outer
        tail <- outer.repeat
      } yield head #:: tail).integral(f)
    }
  }

  /** 
   * This distribution conditioned on occurrence of an event of 
   * positive probability. 
   *
   * Can get very slow if the probability of `event` is low.
   */ 
  def filter(event: X => Boolean): Distribution[X] = new Distribution[X] {
    def sample = {
      val proposal = outer.sample
      if (event(proposal)) proposal else sample
    }
    val eventProbability = prob(event)
    def integral(f: X => Double) = outer.integral{
      x => f(x) * charFct(event)(x)
    } / eventProbability
  }
}

object Distribution {
  /** Just a formality to make the definition of the Giry-monad complete */
  def unit[X](x: X) = Dirac(x)

  /** Transforms predicates into characteristic functions */
  def charFct[X](event: X => Boolean): (X => Double) = {
    x => if (event(x)) 1.0 else 0.0
  }
}

/** Dirac measure (assigns probability `1` to a single outcome) */
case class Dirac[X](constant: X) extends Distribution[X] {
  def sample = constant
  def integral(f: X => Double) = f(constant)
}

/** Coin flip with two outcomes, `true` or `false` */
case class Bernoulli(p: Double = 0.5) extends Distribution[Boolean] {
  private val rnd = new Random
  def sample = rnd.nextDouble < p
  def integral(f: Boolean => Double) = p * f(true) + (1-p) * f(false)
}

/** Same as mapped `Bernoulli` */
case class GenBernoulli[X](t: X, f: X, p: Double = 0.5) extends Distribution[X]{
  private val rnd = new Random
  def sample = if (rnd.nextDouble < p) t else f
  def integral(g: X => Double) = p * g(t) + (1-p) * g(f)
}

/** Uniform distribution on intervals of integers */
case class IntUniform(minIncl: Int, maxExcl: Int) extends Distribution[Int] {
  private val size = maxExcl - minIncl
  private val rnd = new Random
  def sample = minIncl + rnd.nextInt(size)
  def integral(f: Int => Double) = 
    (for (i <- minIncl until maxExcl) yield f(i)).sum / size
}

case class RealUniform(min: Double, max: Double) extends Distribution[Double] {
  private val rnd = new Random
  private val diff = max - min
  def sample = min + rnd.nextDouble * diff
  def integral(f: Double => Double) = ??? // just ordinary integration
}

/** Uniform distribution on finite sets */
case class FiniteUniform[X](values: Array[X]) extends Distribution[X] {
  private val rnd = new scala.util.Random
  private val size = values.size
  def sample = values(rnd.nextInt(size))
  def integral(f: X => Double) = (for (x <- values) yield f(x)).sum
}

/** Non-uniform distribution on finite sets */
class Categorical[X] private (
  val values: Array[X],
  val probabilities: Array[Double],
  val cumulatedProbabilities: Array[Double]
) extends Distribution[X] {

  private val rnd = new Random

  def sample: X = {
    val i = Categorical.infIndex(cumulatedProbabilities, rnd.nextDouble)
    values(i)
  }

  def integral(f: X => Double) = {
    (for ((v,p) <- values zip probabilities) yield f(v) * p).sum
  }
}

object Categorical {

  /**
    * Constructs a finite distribution with given values and weights. 
    * The weights do not have to sum up to 1.
    */
  def apply[X](values: Array[X], weights: Array[Double]): Categorical[X] = {
    require(
      !values.isEmpty, 
      "Attempted to construct Categorical distribution on empty set"
    )
    val totalWeight = weights.sum
    require(totalWeight >= 0)
    require(weights.forall(_ >= 0))
    for (i <- 0 until weights.size) {
      weights(i) /= totalWeight
    }
    val cumulatedProbabilities = 
      weights.scanLeft(0d){(x, y) => x + y}.tail
    // artificially add +\infty to the last element
    cumulatedProbabilities(weights.size-1) += Double.PositiveInfinity
    new Categorical(values, weights, cumulatedProbabilities)
  }

  /**
    * Constructs a finite distribution with given values and probability vector
    */
  def apply[X:ClassTag](valuesProbs: Array[(X, Double)]): Categorical[X] = {
    val (vals, probs) = valuesProbs.unzip
    this.apply(vals.toArray, probs.toArray)
  }

  // This part is surprisingly nasty: 
  // finds the smallest index `i` such that p <= c(i)
  private[Categorical] def infIndex(c: Array[Double], p: Double): Int = {
    val bs = java.util.Arrays.binarySearch(c, p)
    if (bs > 0) {
      // almost infinitely improbable event, but it _can_ occur on real machine
      // we have to walk backward until `c` actually jumps, otherwise we could
      // return an event of probability 0
      var i = bs
      while (c(i) == p && i > 0) i -= 1;
      i
    } else if (bs == 0) {
      0
    } else {
      -bs - 1
    }
  }
}

case class Permutation(mapping: Array[Int]) extends (Int => Int) {
  def apply(i: Int) = mapping(i)
  override def toString = mapping.mkString("(", ",", ")")
  def shuffle[A](v: Vector[A]): Vector[A] = {
    require(mapping.size == v.size)
    Vector.tabulate(v.size){i => v(mapping(i))}
  }
  // exactly the same as above, modulo "JVM-curse": arrays are still aliens...
  def shuffle[A: ClassTag](arr: Array[A]): Array[A] = {
    require(mapping.size == arr.size)
    Array.tabulate(arr.size){i => arr(mapping(i))}
  }
}

case class UniformPermutation(n: Int) extends Distribution[Permutation] {
  private val rnd = new Random
  def sample: Permutation = {
    val mapping = Array.tabulate(n){i => i}
    var tmp: Int = 0
    for (i <- 0 until n) {
      val a = rnd.nextInt(n - i)
      val b = n - 1 - i
      tmp = mapping(a)
      mapping(a) = mapping(b)
      mapping(b) = tmp
    }
    Permutation(mapping)
  }
  def integral(f: Permutation => Double) = ??? // not that important here
}

import scala.collection.mutable.HashSet

/** 
 * Generates a random injective function from `{0,...,a-1}` to `{0,...,b-1}`,
 * represented by an integer array.
 */
case class UniformInjection(a: Int, b: Int)
extends Distribution[Array[Int]] {
  private val rnd = new Random

  private def permutationMethod(a: Int, b: Int): Array[Int] = {
    val mapping = Array.tabulate(b){i => i}
    var tmp: Int = 0
    for (i <- 0 until a) {
      val x = rnd.nextInt(b - i)
      val y = b - 1 - i
      tmp = mapping(x)
      mapping(x) = mapping(y)
      mapping(y) = tmp
    }
    Array.tabulate(a){i => mapping(b - 1 - i)}
  }

  private def retryMethod(a: Int, b: Int): Array[Int] = {
    val chosen = new HashSet[Int]
    val res = new Array[Int](a)
    var i = 0
    while (i < a) {
      val cand = rnd.nextInt(b)
      if (!chosen.contains(cand)) {
        res(i) = cand
        i += 1
        chosen += cand
      }
    }
    res
  }

  def sample = {
    val C_swap = 7
    val C_arr = 2
    val C_hash = 8
    val retryCost = b * C_hash * math.log(b / (b - a + 1).toDouble)
    val permutationCost = C_arr * b + C_swap * a
    if (retryCost < permutationCost){
      retryMethod(a, b) 
    } else {
      permutationMethod(a, b)
    }
  }

  def integral(f: Array[Int] => Double) = ??? 
}

/** 
 * Mixture of finitely many measures is essentially just a two step 
 * experiment: first, we choose a measure, then we sample with respect 
 * to the chosen measure.
 */
class Mixture[X](
  val components: Array[Distribution[X]],
  val weights: Array[Double]
) {
  private val twoStep = 
    for (m <- Categorical(components, weights); x <- m) yield x
  def sample = twoStep.sample
  def integral(f: X => Double) = twoStep.integral(f)
}

/** 
 * Empirical distribution on the real number line.
 *
 * Essentially a mixture of Dirac distributions, 
 * but with an efficient method to compute 
 * empirical cumulative distribution function.
 */
class EmpiricalReal private[EmpiricalReal](points: Array[Double]) 
extends Distribution[Double] {
  private val rnd = new Random
  private val n = points.size
  def sample = points(rnd.nextInt(n))
  def integral(f: Double => Double) = {
    var i = 0
    var sum = 0.0
    while (i < n) {
      sum += f(points(i))
      i += 1
    }
    sum / n
  }
  def cdf(t: Double): Double = {
    var bs = java.util.Arrays.binarySearch(points, t)
    if (bs >= 0) {
      while (bs < (n - 1) && points(bs + 1) == t) bs += 1
      bs += 1
    } else {
      bs = - bs - 1 
    }
    bs.toDouble / n
  }
}

object EmpiricalReal {
  def apply(points: Iterable[Double]): EmpiricalReal = {
    new EmpiricalReal(points.toArray.sorted)
  }
}



/* #############################################################################
   [!]          Stochastic processes and Markov chains
   ###########################################################################*/

/** Time discrete random process */
trait StochasticProcess[X] extends Distribution[Stream[X]] { outer =>

  /** This process, stopped as soon as some predicate is fulfilled */
  def stopped(hittingTimePredicate: X => Boolean): StochasticProcess[X] = {
    new StochasticProcess[X] {
      private def sampleHelper(s: Stream[X]): Stream[X] = {
        val head #:: tail = s
        if (hittingTimePredicate(head)) {
          head #:: Stream.continually(head)
        } else {
          head #:: sampleHelper(tail)
        }
      }
      def sample: Stream[X] = sampleHelper(outer.sample)
      def integral(f: Stream[X] => Double) = ??? // easy, maybe later
    }
  }

  /** pointwise mapping */
  def mapPointwise[Y](f: X => Y): StochasticProcess[Y] = 
  new StochasticProcess[Y] {
    def sample = (for (path <- outer) yield path.map(f)).sample
    def integral(g: Stream[Y] => Double) = {
      outer.integral(path => g(path.map(f)))
    }
  }

  /** pointwise Markov kernel application */
  def flatMapPointwise[Y](f: X => Distribution[Y]): StochasticProcess[Y] = 
  new StochasticProcess[Y] {
    def sample = (for (path <- outer) yield path.map(x => f(x).sample)).sample
    def integral(g: Stream[Y] => Double) = ??? // possible, but not needed now
  }

  /** pointwise zipping with other proccess */
  def zipPointwise[Y](other: StochasticProcess[Y]): StochasticProcess[(X,Y)] = {
    new StochasticProcess[(X,Y)] {
      def sample = 
        (for (a <- outer; b <- other) yield (a zip b)).sample
      def integral(g: Stream[(X,Y)] => Double) = ??? // possible, not needed now
    }
  }
}

/** 
 * Time discrete `X`-valued Markov chain.
 * 
 */
trait MarkovChain[X] extends StochasticProcess[X] { outer => 
  /** Returns the initial distribution */
  def initial: Distribution[X]
  def next(current: X): Distribution[X]
  
  /** Starts a new Markov chain at `x` */
  def startAt(x: X): StochasticProcess[X] = new StochasticProcess[X] {
    // private val law = for {     // It looks correct, but it's not...
    //   y <- outer.next(x)
    //   tail <- outer.startAt(y)
    // } yield x #:: tail

    private def sampleTail(head: X): Stream[X] = {
      val tailStart = outer.next(head).sample
      tailStart #:: sampleTail(tailStart)
    }

    def sample = x #:: sampleTail(x)

    def integral(f: Stream[X] => Double) = ??? // This seems rather difficult? 
  }

  private val combinedLaw = {
    val blah = initial
    for (i <- initial; path <- startAt(i)) yield path
  }

  /** 
   * Starts a Markov chain with first valued chosen according to 
   * the initial distribution
   */
  def sample = combinedLaw.sample
  def integral(f: Stream[X] => Double) = combinedLaw.integral(f)
}

/** A deterministic function reinterpreted as stochastic process */
abstract class DeterministicFunction[X] extends StochasticProcess[X] {
  def apply(t: Int): X 
  def sample = Stream.from(0).map(t => this(t))
  def integral(f: Stream[X] => Double) = f(sample)
}

/** 
 * Time-discrete random walk that is reflected 
 * at the bounds `min` and `max`. 
 */
class BoundedRandomWalk(min: Double, max: Double, jump: Double) extends {
  val initial = RealUniform(min, max)
} with MarkovChain[Double] {
  require(jump < (max - min))
  def next(current: Double) = {
    if (current + jump >= max) Dirac(current - jump)
    else if (current - jump <= min) Dirac(current + jump)
    else GenBernoulli(current + jump, current - jump)
  }
}

/* #############################################################################
   [!]                          Statistics
   ###########################################################################*/

/** 
 * A statistic of type `X,Y` is anything that can consume samples of type `X`
 * and process them on the fly, yielding values of type `Y` in the end.
 * 
 * For example, a structure that can consume lot of real numbers, and 
 * return their average in the end, is a statistic.
 * A statistic should not occupy too much memory, if possible.
 */
trait Statistic[-X, +Y] { outer => 
  def consume(x: X): Unit
  def result: Y
  def prepend[Z](f: Z => X): Statistic[Z, Y] = new Statistic[Z, Y] {
    def consume(z: Z) = outer.consume(f(z))
    def result = outer.result
  }
  def map[Z](f: Y => Z): Statistic[X, Z] = new Statistic[X, Z] {
    def consume(x: X) = outer.consume(x)
    def result = f(outer.result)
  }
}

class RealAverage extends Statistic[Double, Double] {
  private var sum: Double = 0.0
  private var number: Long = 0L
  def consume(x: Double) = { sum += x; number += 1 }
  def result = sum / number
}

class EcdfStatistic extends Statistic[Double, EmpiricalReal] {
  private var allValues: List[Double] = Nil
  def consume(x: Double) = { allValues ::= x }
  def result = EmpiricalReal(allValues.toArray)
}

/* #############################################################################
   [!]                          Partitions 
   ###########################################################################*/

import scala.collection.immutable.Set

/** Extensional representation of a partition */
case class Partition[X](sets: Set[Set[X]]) {
  override def toString = {
    sets.map{
      _.toList.map{_.toString}.sorted.mkString("{", ",", "}")
    }.toList.sorted.mkString("{", ",", "}")
  }

  def totalSet = sets.flatten
}

object Partition {

  /** Transforms an intensional representation of a partition into
    * an extensional representation 
    * (This is essentially the function `\mathcal{E}`)
    */
  def groupBy[X, Y](what: Iterable[X], byWhat: X => Y): Partition[X] = {
    val sets = what.toSet.groupBy(byWhat).values.toSet
    Partition(sets)
  }

  def coarsest[X](total: Set[X]): Partition[X] = Partition(Set(total))
  def finest[X](total: Set[X]): Partition[X] = 
    Partition(total.map{ x => Set(x) })
}






/* #############################################################################
   [!]                        Random populations
   ###########################################################################*/

/* The goal of this chunk of code is to model (potentially) infinite streams
 * of populations, without specifying any parentship relationships between 
 * different generations.
 */

// A population is described by 
// - the number of families, 
// - an array of single-byte `FamilyDescriptor`s,
// - a `FamilyStructure`, that knows how to interpret the `FamilyDescriptors`
type FamilyDescriptor = Byte

// The complete information about a random coalescent consists of a sequence
// of arrays with integer-triples as entries. Each triple contains the 
// following information:
//  - family index
//  - index of individual within family
//  - index of chromosome within individual
type FamilyIdx = Short
type IndividualIdx = Byte
type ChromosomeIdx = Byte

/** 
 * A `FamilyStructure` describes possible types of families in a population.
 * In some models (for example, monogamous 'Swedish family' model), there will
 * be just one type of family. However, for example for "alien bees",
 * there will be multiple types of families, depending on the number of 
 * haploid males: `(1 queen, 1 male)`, `(1 queen, 2 males)`, ..., 
 * `(1 queen, 255 males)`.
 */
trait FamilyStructure {
  def numParents(descriptor: FamilyDescriptor): Int
  def maxNumParents: Int
  def randomDescriptor: Distribution[FamilyDescriptor]
  def familyToString(descriptor: FamilyDescriptor): String
  def fullCoordToString(f: FamilyIdx, i: IndividualIdx, c: ChromosomeIdx) = 
    "(f=%d,i=%d,c=%d)".format(f, i, c)

  /** Suppose that we know that the parent family of an individual with
   *  index `i` (internal index within family structure) is of type `parent`.
   *  What are the possible ways for the individual `i` to inherit its 
   *  chromosomes from its parents?
   *
   *  For example, in the monogamous diploid model with one male and one female
   *  as parents, there are four possible, equally probable assignments of the
   *  inherited chromosomes. If we mark father's chromosomes by `(a,b)` and
   *  mother's chromosomes by `(c,d)`, then possible outcomes are:
   *  `(a,c)`, `(a,d)`, `(b,c)` and `(b,d)`.
   */
  def chromosomeInheritance(
    i: IndividualIdx,
    parent: FamilyDescriptor
  ): Distribution[ChromosomeInheritance]

  /** Supposing that a lineage is tracked far enough into the past,
   *  and it ends up in a family with the specified `descriptor`.
   *  Which individual and which chromosome will the lineage hit with 
   *  what probability?
   *
   *  For example, if there is one father and one mother, both diploid,
   *  then each chromosome will be hit with probability `1/4`.
   *  On the other hand, if we have one diploid queen and `D` haploid drones,
   *  then each chromosome of the queen will be hit with probability `1/3`,
   *  while each drone will be hit with probability `1/3D`.
   */
  def equilibriumLineagePosition(
    descriptor: FamilyDescriptor
  ): Distribution[(IndividualIdx, ChromosomeIdx)]
}

/**
 * For all our models, a family has essentially just one property: 
 * a natural number of "parents" (for example, number of drones + 1 queen for
 * the bees/wasps). Therefore, a population is described by the number of
 * families, and a single integer for each family (we shall call such an
 * integer a "family descriptor").
 * It's reasonable to assume that there aren't too many "family types" in each
 * model, we restrict it to 256 in order to keep the representation compact. 
 */
case class Population(
  familyStructure: FamilyStructure,
  familyDescriptors: Array[FamilyDescriptor]
) {
  def numFamilies = familyDescriptors.size
  lazy val numIndividuals = familyDescriptors.map{
    d => familyStructure.numParents(d)
  }.sum
  override def toString = familyDescriptors.map{
    d => familyStructure.familyToString(d)
  }.mkString("Population[",",","]")
  def apply(f: FamilyIdx) = familyDescriptors(f)
}

/** 
 * Generates an infinite stream of populations.
 * Each population consists of a bunch of families, determined by their
 * descriptors.
 * The number of families is determined by the process `numberOfFamilies`.
 */
def randomPopulationHistory(
  numberOfFamilies: StochasticProcess[Int],
  familyStructure: FamilyStructure
): StochasticProcess[Population] = numberOfFamilies.flatMapPointwise{
  n => familyStructure.randomDescriptor.pow(n).map{
    v => Population(familyStructure, v.toArray)
  }
}

/* #############################################################################
   [!]                        Random pedigrees
   ###########################################################################*/

/* 
 * Now we build random pedigrees on top of random population histories,
 * by specifying parentship relations between adjacent generations.
 */

/** A `ParentFamilyChoice` is a data structure which, for each given 
  * individual `(f,i)` (individual from family `f`, with individual index `i`),
  * stores an index of a parent family from previous generation.
  */
class ParentFamilyChoice (
  val childPopulation: Population,
  val parentPopulation: Population
) extends ((FamilyIdx, IndividualIdx) => FamilyIdx) {

  private val numFamilies = childPopulation.numFamilies
  private val maxNumParents = parentPopulation.familyStructure.maxNumParents

  private val parentFamily: Array[FamilyIdx] = {
    new Array[FamilyIdx](numFamilies * maxNumParents)
  }

  def update(f: FamilyIdx, i: IndividualIdx, pf: FamilyIdx): Unit = {
    parentFamily(f * maxNumParents + i) = pf
  }

  def apply(f: FamilyIdx, i: IndividualIdx): FamilyIdx = 
    parentFamily(f * maxNumParents + i)

  override def toString = {
    parentFamily.grouped(maxNumParents).map{
      _.mkString(",")
    }.mkString("PFC(","|",")")
  }
}

/** A `OffspringNumberDistributionFactory` takes two inputs: 
  * total number of individuals in the current generation, and
  * number of families in the previous generation. 
  * It returns a distribution of an `Array[Int]` valued random variable, such
  * that the size of the array corresponds to the number of families, the
  * sum of entries of the array is equal to the total number of individuals,
  * and furthermore, the entries of the array are exchangeable, 
  * natural-number-valued random variables.
  */
trait OffspringNumberDistributionFactory {
  def apply(
    currentNumIndividuals:Int, 
    previousNumFamilies: Int
  ): Distribution[Array[Int]]

  /** This is essentially `\Phi_1(2)` */
  def sameFamilyChoiceProbability(
    currentNumInviduals: Int,
    previousNumFamilies: Int
  ): Double
}

object WrightFisherFactory 
extends OffspringNumberDistributionFactory {
  /** 
   * Builds a special case of multinomial distribution, with all outcomes
   * having the same probability.
   */
  def apply(currentNumIndividuals: Int, previousNumFamilies: Int) = {
    new Distribution[Array[Int]] {
      val rnd = new Random
      def sample = {
        val res = new Array[Int](previousNumFamilies)
        for (i <- 0 until currentNumIndividuals) {
          res(rnd.nextInt(previousNumFamilies)) += 1
        }
        res
      }
      def integral(f: Array[Int] => Double) = ??? // irrelevant...
    }
  }
  /** `\Phi_1(2)` */
  def sameFamilyChoiceProbability(
    currentNumIndividuals: Int,
    previousNumFamilies: Int
  ) = 1.0 / previousNumFamilies
}

/** 
 * A random pedigree is a `ParentFamilyChoice`-valued stochastic process,
 * that is, it tells for each individual in each family in each generation 
 * what parent-family to choose.
 */
def randomPedigree(
  generations: Stream[Population],
  offspringNumberFactory: OffspringNumberDistributionFactory
): StochasticProcess[ParentFamilyChoice] = 
  new StochasticProcess[ParentFamilyChoice] {
  def sample = {
    val currentGenerations = generations
    val parentGenerations = currentGenerations.tail
    val adjacentGenerations = currentGenerations zip parentGenerations
    for ((curr, prev) <- adjacentGenerations) yield {
      val offspringNumbers = 
        offspringNumberFactory(curr.numIndividuals, prev.numFamilies).sample
      val sigma = UniformPermutation(curr.numIndividuals).sample
      val q = (for (
        (famIdx, numOff) <- (0 until prev.numFamilies) zip offspringNumbers;
        x <- Array.fill[FamilyIdx](numOff)(famIdx.toShort)
      ) yield x).toArray
      assert(q.forall{x => x >= 0},
        "prev.numFamilies = " + prev.numFamilies + "\n" +
        "q = " + q.mkString(",")
      )
      val qSigma = sigma.shuffle(q)
      assert(qSigma.forall{x => x >= 0})
      var r = 0
      val pfc = new ParentFamilyChoice(curr, prev)
      for (f <- (0 until curr.numFamilies).map(_.toShort).toArray) yield {
        val numPrts = curr.familyStructure.numParents(curr.familyDescriptors(f))
        for (i <- (0 until numPrts).map(_.toByte).toArray) yield {
          val parentFamilyIdx = qSigma(r)
          r += 1
          pfc(f, i) = parentFamilyIdx 
        }
      }
      pfc
    }
  }
  def integral(f: Stream[ParentFamilyChoice] => Double) = ??? // impractical
}

/** 
 * Population structure defines an an increasing process
 * that corresponds to the internal time of the Kingman's coalescent.
 * 
 * The following process defines time increments.
 */
def virtualTimeIncrements(
  generations: Stream[Population],
  offspringNumberFactory: OffspringNumberDistributionFactory,
  familyStructure: FamilyStructure
): Stream[Double] = {
  // This is `c_N` divided by `\Phi_1(2)`: we don't have to compute it
  // manually, the Giry-monad does this job for us.
  val averageSameChromosomeChoiceProb = 
    (for {
      descr <- familyStructure.randomDescriptor
      firstLineage <- familyStructure.equilibriumLineagePosition(descr)
      secondLineage <- familyStructure.equilibriumLineagePosition(descr)
    } yield (firstLineage == secondLineage)).prob{ b => b }

  for ((curr, prev) <- generations zip generations.tail) yield {
    val phi12 = offspringNumberFactory.sameFamilyChoiceProbability(
      curr.numIndividuals, 
      prev.numFamilies
    )
    phi12 * averageSameChromosomeChoiceProb // This is our c_N
  }
}

/** 
 * Cumulated sums of time increments
 */
def virtualTime(
  generations: Stream[Population],
  offspringNumberFactory: OffspringNumberDistributionFactory,
  familyStructure: FamilyStructure
): Stream[Double] = {
  val deltas = virtualTimeIncrements(
    generations, 
    offspringNumberFactory, 
    familyStructure
  )
  deltas.scanLeft(0d){ case (prevSum, entry) => prevSum + entry }
}

/* #############################################################################
   [!]                   Coalescents in random pedigrees 
   ###########################################################################*/

/* Now we can simulate random coalescents in random pedigrees.
 * We need a way to represent the outcomes of the 
 * Mendelian randomness experiments. 
 * This is what `ChromosomeInheritance` is for.
 */

/** 
 * A `ChromosomeInheritance` is a function that determines how the genome of 
 * an individual is composed from the genome of individual's parents.
 * 
 * It takes the index of a choromosome of the individual as input, and 
 * returns index of the parent, as well as index of a chromosome within the
 * parent, that is copied by the individual.
 *
 * Example: Suppose we have a diploid individual (with chromosomes numbered 
 * 0 and 1)
 * Suppose its parent family consists of a diploid mother (individual index 0)
 * and a diploid father (with individual index 1).
 * Then 
 * {{{
 *   f(0) = (0,1)
 *   f(1) = (1,0)
 * }}}
 * would be a valid `ChromosomeInheritance` function. It would tell us, that
 * the first chromosome of the individual is the same as the second chromosome
 * of the mother, and the second chromosome is the same as the first chromosome
 * of the father.
 */
trait ChromosomeInheritance 
extends (ChromosomeIdx => (IndividualIdx, ChromosomeIdx))

/** 
 * Special `ChromosomeInheritance` for haploid individuals.
 * Since there is just one chromosome, its index can be ignored.
 */
case class ConstInheritance(i: IndividualIdx, c: ChromosomeIdx) 
extends ChromosomeInheritance {
  def apply(ignored: ChromosomeIdx) = (i, c)
}

/**
 * Completely describes predecessors of a sample.
 * Corresponds to values of `X^{N,n}_g` in the proof. 
 */
case class FullState(
  state: Array[(FamilyIdx, IndividualIdx, ChromosomeIdx)],
  familyStructure: Option[FamilyStructure] = None // not strictly necessary
) {
  override def toString = if (familyStructure.isEmpty) {
    state.mkString("Full[",",","]")
  } else {
    state.map{x => familyStructure.get.fullCoordToString(x._1, x._2, x._3)}.
    mkString("Full[",";","]")
  }
  def toPartition: Partition[Int] = Partition.groupBy(
    0 until state.size, idx => state(idx)
  )
  def apply(i: Int) = state(i)
  def sampleSize = state.size
}

// Corresponds to the process `(X^{N,n}_g)_g` in the proof.
def fullCoalescentHistory(
  sampleSize: Int,
  pedigree: Stream[ParentFamilyChoice]
): StochasticProcess[FullState] = new StochasticProcess[FullState] {
  
  private def mendelianSampling(
    relevantIndividualCoords: Set[(FamilyIdx, IndividualIdx)],
    pfc: ParentFamilyChoice
  ): Map[(FamilyIdx, IndividualIdx), ChromosomeInheritance] = {
    (for ((f, i) <- relevantIndividualCoords) yield {
      // what is the parent family of the individual `(f,i)`?
      val predFamIdx = pfc(f, i) 
      // get the descriptor of the parent family from `ParentFamilyChoice`
      val predFamDescr = pfc.parentPopulation(predFamIdx)
      // use the `FamilyStructure` to obtain the law of Mendelian 
      // inheritance for this individual and this family type
      val familyStructure = pfc.parentPopulation.familyStructure
      val mendelianLaw = 
        familyStructure.chromosomeInheritance(i, predFamDescr)
      // sample an assignment of chromosomes to parents and their 
      // chromosomes
      val chromosomeInheritance = mendelianLaw.sample
      ((f, i), chromosomeInheritance)
    }).toMap
  }

  private def sampleHelper(
    startingAt: FullState, 
    remainingPedigree: Stream[ParentFamilyChoice]
  ): Stream[FullState] = {
    remainingPedigree.scanLeft(startingAt){ (s, pfc) => 
      val relevantIndividualCoords: Set[(FamilyIdx, IndividualIdx)] = 
        s.state.map{ x => (x._1, x._2) }.toSet
      val relevantMendelianOutcomes = 
        mendelianSampling(relevantIndividualCoords, pfc)
      val newFullState = Array.tabulate(s.sampleSize){ i => 
        // what chromosome does `i`'th marker point to?
        val (famIdx, indIdx, chrIdx) = s(i) 
        // what is the parent family of the individual `(famIdx,indIdx)`?
        val predFamIdx = pfc(famIdx, indIdx) 
        // what is the relevant outcome of the Mendelian experiment?
        val chromosomeInheritance = relevantMendelianOutcomes((famIdx, indIdx))
        // use the chromosomeInheritance to obtain parent index and index of
        // the chromosome within parent
        val (predIndIdx, predChrIdx) = chromosomeInheritance(chrIdx)
        // combine family index with parent index and chromosome index into
        // a new, completely unambiguous, coordinate of the `i`'th marker
        (predFamIdx, predIndIdx, predChrIdx)
      }
      FullState(newFullState, Some(pfc.parentPopulation.familyStructure))
    }
  }

  def sample = {
    // start with a uniform injection
    val firstNumFamilies = pedigree(0).childPopulation.numFamilies
    val law_x0 = 
    for (j <- UniformInjection(sampleSize, firstNumFamilies)) yield {
      FullState(
        Array.tabulate(sampleSize){i => (j(i).toShort, 0.toByte, 0.toByte)},
        Some(pedigree(0).parentPopulation.familyStructure)
      )
    }
    val realization_x0 = law_x0.sample

    // use the sample helper to continue the stream
    sampleHelper(realization_x0, pedigree)
  }

  def integral(f: Stream[FullState] => Double) = ??? // impractical
}

// Corresponds to `(\mathfrak{X}^{N,n}_g)_g` in the proof
def partitionCoalescentHistory(
  sampleSize: Int,
  pedigree: Stream[ParentFamilyChoice]
): StochasticProcess[Partition[Int]] = 
  fullCoalescentHistory(sampleSize, pedigree).mapPointwise(_.toPartition)




/* #############################################################################
   [!]               States and holding times representation
   ###########################################################################*/

/** 
 * State and holding time representation of a coalescent.
 * The lists `states` and `holdingTimes` store only the relevant entries
 * `S_2,S_3,...,S_n` and `H_2,H_3,...,H_n`.
 */
class StatesHoldingTimes(
  val sampleSize: Int,
  val states: List[Partition[Int]],
  val holdingTimes: List[Double]
) {
  def mrcaTime = holdingTimes.sum
  override def toString = {
    (for ((h,s) <- (holdingTimes zip states).reverse) yield {
      "%2.3f %s".format(h,s)
    }).mkString("StatesTimes[\n  ","\n  ","\n|") +
    " mrcaTime = " + holdingTimes.sum + "]"
  }
}

object StatesHoldingTimes {
  /** 
   * Builds a states-and-holding-times representation 
   * from a stream of partitions and the virtual time.
   */
  def apply(
    sampleSize: Int,
    partitionHistory: Stream[Partition[Int]],
    virtualTime: Stream[Double]
  ): StatesHoldingTimes = {
    var lastSize = sampleSize + 1
    var lastJumpTime = -42.0
    var lastState = Partition.finest((0 to sampleSize).toSet)
    var states: List[Partition[Int]] = Nil
    var holdingTimes: List[Double] = Nil
    for ((s, t) <- partitionHistory zip virtualTime) {
      if (lastSize > s.sets.size) {
        // jump detected
        while (lastSize > s.sets.size) {
          holdingTimes ::= (t - lastJumpTime)
          lastJumpTime = t
          states ::= s
          lastSize -= 1
        }
        if (s.sets.size == 1) {
          return new StatesHoldingTimes(
            sampleSize,
            states.tail,
            holdingTimes.take(sampleSize - 1)
          )
        }
      }
    }
    throw new RuntimeException("Unexpectedly reached end of infinite stream.")
  }
}

val Venus = '\u2640'   // female
val Mars = '\u2642'    // male 
val Mercury = '\u263F' // hermaphrodite

/* #############################################################################
   [!]                            Meme model
   ###########################################################################*/

object MemeFamilyStructure extends FamilyStructure {
  def numParents(ignore: Byte) = 2
  def maxNumParents = 2
  def randomDescriptor = Dirac(0.toByte) // there is only one type of family
  def familyToString(ignore: Byte) = "" + Venus + Mars
  def chromosomeInheritance(i: IndividualIdx, parentFamilyDescriptor: Byte): 
    Distribution[ChromosomeInheritance] = {
    // structure of parent family is always the same, `i` is also irrelevant:
    // we always just copy the meme either from mother, or from father.
    // Since both mother and father are "meme-haploid", the "chromosome"-index
    // is always 0.
    GenBernoulli(
      ConstInheritance(0,0), // inherit 0-th meme from mother
      ConstInheritance(1,0)  // or 0-th meme from father
    )
  }
  def equilibriumLineagePosition(d: FamilyDescriptor): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = 
      for (i <- GenBernoulli(0, 1)) yield (i.toByte, 0.toByte)

  override def fullCoordToString(
    f: FamilyIdx, 
    i: IndividualIdx, 
    c: ChromosomeIdx
  ) = "(%d,%s)".format(f, (if (i == 0) ("" + Venus) else ("" + Mars)))
}

/* #############################################################################
   [!]                      'Swedish families' model
   ###########################################################################*/

case class DiploidInheritance(
  motherChromosome: ChromosomeIdx, 
  fatherChromosome: ChromosomeIdx
) extends ChromosomeInheritance {
  def apply(ci: ChromosomeIdx) = 
    if (ci == 0) (0.toByte, motherChromosome) 
    else         (1.toByte, fatherChromosome)
}

object DukeFamilyStructure extends FamilyStructure {
  def numParents(ignore: FamilyDescriptor) = 2
  def maxNumParents = 2
  def randomDescriptor = Dirac(0.toByte)
  def familyToString(ignore: FamilyDescriptor) = "" + Venus + Mars
  def chromosomeInheritance(i: IndividualIdx, parentFamilyDescriptor: Byte): 
    Distribution[ChromosomeInheritance] = {
    // without restriction of generality, the first gene is always 
    // inherited from mother, the second from father
    FiniteUniform(Array(
      DiploidInheritance(0.toByte, 0.toByte),      
      DiploidInheritance(0.toByte, 1.toByte),      
      DiploidInheritance(1.toByte, 0.toByte),
      DiploidInheritance(1.toByte, 1.toByte)
    ))
  }
  def equilibriumLineagePosition(ignored: FamilyDescriptor): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = 
      for {
        i <- GenBernoulli(0.toByte, 1.toByte)
        c <- GenBernoulli(0.toByte, 1.toByte)
      } yield (i, c)

  override def fullCoordToString(
    f: FamilyIdx, 
    i: IndividualIdx, 
    c: ChromosomeIdx
  ) = "(%d,%s,%s)".format(f, 
    (if (i == 0.toByte) ("" + Venus) else ("" + Mars)),
    c.toInt
  )
}

/* #############################################################################
   [!]                        Polygynous fish model
   ###########################################################################*/

case class FishInheritance(
  fatherChromosome: ChromosomeIdx,
  motherIdx: IndividualIdx,
  motherChromosome: ChromosomeIdx
) extends ChromosomeInheritance {
  def apply(ci: ChromosomeIdx) = 
    if (ci == 0) (0.toByte, fatherChromosome) 
    else         (motherIdx, motherChromosome)
}

/** 
 * Family consisting of a single diploid father-fish
 * and a uniformly chosen number of `minFemales` to `maxFemales` 
 * diploid females.
 * 
 * Father-fish has index 0.
 * Females are numbered 1 to `maxFemales`.
 * Family descriptor `d` corresponds to a family with `d` females.
 * The descriptor `d=0` should never occur.
 */
case class FishFamilyStructure(minFemales: Byte, maxFemales: Byte) 
extends FamilyStructure {
  require(minFemales > 0, 
    "A fish family needs at least one female, but minFemales = " + minFemales)
  require(maxFemales >= minFemales, 
    "Inconsistency: minFemales = " + minFemales + 
    " maxFemales = " + maxFemales)
  def numParents(d: FamilyDescriptor) = (d.toInt + 1)
  def maxNumParents = maxFemales.toInt + 1
  def randomDescriptor = IntUniform(minFemales, maxFemales + 1).map{_.toByte}
  def familyToString(d: FamilyDescriptor) = Mars + ("" + Venus) * d.toInt
  def chromosomeInheritance(i: IndividualIdx, d: FamilyDescriptor): 
    Distribution[ChromosomeInheritance] = {
    // without restriction of generality, the first gene is 
    // inherited from the father-fish, the other gene is 
    // inherited from the uniformly chosen mother-fish.
    for {
      fc <- GenBernoulli(0.toByte, 1.toByte)
      m <- IntUniform(0, d).map{ _ + 1 }
      mc <- GenBernoulli(0.toByte, 1.toByte)
    } yield FishInheritance(fc, m.toByte, mc)
  }

  private def equilibriumHelper(d: FamilyDescriptor)(lineageInFather: Boolean): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = {
    if (lineageInFather) {
      GenBernoulli((0.toByte, 0.toByte), (0.toByte, 1.toByte))    
    } else {
      for {
        m <- IntUniform(0, d).map{ _ + 1 }
        res <- GenBernoulli(0,1).map{ x => (m.toByte, x.toByte) }
      } yield res
    }
  }

  private val EquilibriumLineageInMaleProb = 0.5
  def equilibriumLineagePosition(d: FamilyDescriptor): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = 
      Bernoulli(EquilibriumLineageInMaleProb).flatMap{
        l => equilibriumHelper(d)(l)
      }

  override def fullCoordToString(
    f: FamilyIdx, 
    i: IndividualIdx, 
    c: ChromosomeIdx
  ) = "(%d,%s,%s)".format(f, 
    (if (i == 0.toByte) ("" + Mars) else ("" + Venus + i)),
    c.toInt
  )
}

/* #############################################################################
   [!]                         Alien-ants model 
   ###########################################################################*/

// Ants have two different inheritance mechanisms for queen and drones.
// Since drones are haploid, we can reuse `ConstInheritance` defined above,
// but the queen needs yet another inheritance strategy.

/** 
 * A queen inherits one chromosome from it's mother queen, and 
 * one chromosome from a particularly lucky drone. 
 * Since there is only one queen, we need only queen chromosome index.
 * Since every drone is haploid, we need only drone's individual index.
 */
case class AntQueenInheritance(
  queenChromosomeIdx: ChromosomeIdx,
  luckyDroneIdx: IndividualIdx
) extends ChromosomeInheritance {
  def apply(ci: ChromosomeIdx) = 
    if (ci == 0) (0.toByte, queenChromosomeIdx)
    else         (luckyDroneIdx, 0.toByte)
}

/** 
 * Fertile individuals that contribute to the genome of a colony are:
 *  - a single diploid female queen
 *  - multiple haploid male drones 
 * There can be between `minDrones` and `maxDrones` drones.
 * 
 * Queen has individual index 0.
 * Drones are numbered with indices 1 to `maxDrones` (inclusively).
 * Family descriptor `d` corresponds to a colony with `d` drones.
 * The descriptor `d=0` should never occur.
 */
case class AntsColonyStructure(minDrones: Byte, maxDrones: Byte) 
extends FamilyStructure {
  require(minDrones > 0, 
    "An ant colony needs at least one drone, but minDrones = " + minDrones)
  require(maxDrones >= minDrones, 
    "Inconsistency: minDrones = " + minDrones + 
    " maxDrones = " + maxDrones)
  def numParents(d: FamilyDescriptor) = (d.toInt + 1)
  def maxNumParents = maxDrones.toInt + 1
  def randomDescriptor = IntUniform(minDrones, maxDrones + 1).map{_.toByte}
  def familyToString(d: FamilyDescriptor) = Venus + ("" + Mars) * d.toInt
  def chromosomeInheritance(i: IndividualIdx, d: FamilyDescriptor): 
    Distribution[ChromosomeInheritance] = {
    // queen and drones are quite different beasts... treat them separately
    if (i == 0) {
      // queen
      for {
        qci <- GenBernoulli(0.toByte, 1.toByte)
        lucky <- IntUniform(0, d).map{ _ + 1 }
      } yield AntQueenInheritance(qci, lucky.toByte)
    } else {
      // all drones are kind-of half-clones of the queen
      for {
        qci <- GenBernoulli(0.toByte, 1.toByte)
      } yield ConstInheritance(0.toByte, qci)
    }
  }

  private def equilibriumHelper(d: FamilyDescriptor)(lineageInQueen: Boolean): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = {
    if (lineageInQueen) {
      GenBernoulli((0.toByte, 0.toByte), (0.toByte, 1.toByte))    
    } else {
      IntUniform(0, d).map{ i => ((i + 1).toByte, 0.toByte) }
    }
  }

  private val EquilibriumLineageInQueenProb = 2.0 / 3.0
  def equilibriumLineagePosition(d: FamilyDescriptor): 
    Distribution[(IndividualIdx, ChromosomeIdx)] = 
      Bernoulli(EquilibriumLineageInQueenProb).flatMap{
        l => equilibriumHelper(d)(l)
      }

  override def fullCoordToString(
    f: FamilyIdx, 
    i: IndividualIdx, 
    c: ChromosomeIdx
  ) = "(%d,%s,%s)".format(f, 
    (if (i == 0.toByte) ("" + Venus) else ("" + Mars + i)),
    c.toInt
  )
}






/* #############################################################################
   [!]                          Code formatting
   ###########################################################################*/

/* 
 * The code in this section makes some cosmetic changes on the code itself:
 * it skims through the file, finds all lines marked by a exclamation mark in
 * square brackets, and inserts a simple line-based index at the beginning of
 * the file.
 *
 * It has nothing to do with genetics or stochastic processes whatsoever.
 */
import scala.io.StdIn.readLine
val SectionTag = "]![".reverse

/** Reads source code from std-in, inserts an actualized index between
  * the INDEX-tags at the beginning of the file.
  */
def createIndex(): Unit = {
  var line: String = ""
  var state = "beforeIndex"
  var beforeIndex: List[String] = Nil
  var afterIndex: List[String] = Nil
  var sections: List[(String,Int)] = Nil
  var lineNumber = 1
  while ({line = readLine(); line != null}) {
    state match {
      case "beforeIndex" => {
        if(line.contains("[INDEX]")) {
          state = "skippingIndex"
        }
        beforeIndex ::= line
        lineNumber += 1
      }
      case "skippingIndex" => {
        if (line.contains("[/INDEX]")) {
          state = "normal"
          afterIndex ::= line
          lineNumber += 1
        }
      }
      case "normal" => {
        if (line.contains(SectionTag)) {
          val title = line.drop(line.indexOf(SectionTag) + 3).trim
          sections ::= (title, lineNumber)
        }
        afterIndex ::= line
        lineNumber += 1
      }
    }
  }
  for (l <- beforeIndex.reverse) println(l)
  println()
  for ((title, lineNumber) <- sections.reverse) {
    val lineString = "" + (lineNumber + sections.size + 2)
    print(title)
    print("." * (80 - title.size - lineString.size))
    println(lineString)
  }
  println()
  for (l <- afterIndex.reverse) println(l)
}

/* #############################################################################
   [!]                      Parameter parsing
   ###########################################################################*/

// Just parsing command line arguments, 
// nothing particularly interesting here... 

class ArgsOption(
  val names: List[String], 
  val help: String, 
  val default: String,
  val isFlag: Boolean = false,
  val regex: String = "[-_,0-9a-zA-Z()]+"
) {
  var value: Option[String] = None
  def immediateAction(): Unit = {}
  def get: String = value.getOrElse{default}
  def set(a: String): Unit = { value = Some(a) }
  override def toString = names.mkString("/")
  def verboseDescription: String = {
    names.sortBy(_.size).last + " = " + get
  }
}

class ArgsOptions(opts: List[ArgsOption]) {
  def parse(arguments: Array[String]): Unit = {
    var justParsed: Option[ArgsOption] = None
    for (a <- arguments) {
      if (!justParsed.isEmpty && !justParsed.get.isFlag) {
        if (a.matches(justParsed.get.regex)) {
          justParsed.get.set(a)
          justParsed = None
        } else {
          println("Invalid argument for option '" + justParsed.get + "':")
          println(">>>" + a + "<<<")
          println("Expected regex: " + justParsed.get.regex)
          System.exit(1)
        }
      } else {
        opts.find{ o => o.names.contains(a) } match {
          case None => {
            println("Unrecognized option >>>" + a + "<<<")
            System.exit(1)
          }
          case Some(o) => {
            justParsed = Some(o)
            o.immediateAction()
            if (o.isFlag) o.set("true")
          }
        }
      }
    }
  }

  /** 
   * Returns modification of this `ArgsOptions` with one
   * additional, automatically generated help option.
   */
  def withHelp(
    generalHelpIntro: String,
    generalHelpOutro: String 
  ): ArgsOptions = {
    val helpOption = new ArgsOption(
      List("-h", "-?", "--help", "-help"),
      "Prints this help and exits", "false",
      true
    ) {
      override def immediateAction = {
        println(generalHelpIntro)
        for (o <- opts) {
          println(" " + o.names.mkString(" / "))
          val indented = (
            for (l <- o.help.split("\n")) yield ("     " + l)
          ).mkString("\n")
          println(indented)
        }
        println(generalHelpOutro)
        System.exit(0)
      }
    }
    new ArgsOptions(helpOption :: opts)
  }

  def apply(optName: String): String = { 
    opts.find{_.names.contains(optName)} match {
      case Some(hit) => hit.get
      case None => {
        println("Could not find value for command line option " + optName)
        System.exit(0)
        throw new Exception
      }
    }
  }

  def verboseDescription: String = {
    (for (o <- opts) yield {
      o.verboseDescription
    }).mkString("\n")
  }
}

val createIndexOption = new ArgsOption(
  List("--create-index"),
  "Reads source code from STDIN, outputs formatted source code with added " +
  "index to STDOUT.", "false", true
) {
  override def immediateAction(): Unit = {
    createIndex()
    System.exit(0)
  }
}

val cli = new ArgsOptions(List(
  new ArgsOption(List("--pedigrees","-p"), 
    "Number of generated pedigrees.\nDefault: '-p 10'", "10",
    false, "[1-9][0-9]*"),
  new ArgsOption(List("--coalescents","-c"), 
    "Number of sampled coalescents.\nDefault: '-c 256'", "256",
    false, "[1-9][0-9]*"),
  new ArgsOption(List("--sample-size","-n"), 
    "Sample size.\nDefault: '-n 2'", "2",
    false, "[1-9][0-9]*"),
  new ArgsOption(List("--num-families","-N"), 
    "Number of families per generation.\nDefault: '-N 100'", "100",
    false, "[1-9][0-9]*"),
  new ArgsOption(List("--num-families-variation"),
    "Relative variation of number of families.\nDefault: 0\n" +
    "Examples: '--num-families 1000 --num-families-variation 0.5' will \n" +
    "produce a pedigree where the number of families per generation varies\n" +
    "between 500 and 1500. Accepts only numbers from [0,1).",
    "0.0", false, "0\\.[0-9]+"
  ),
  new ArgsOption(List("--model","-m"), 
    "Family model. Available options are:\n" +
    "  Meme\n" + 
    "  Duke\n" +
    "  Fish(<minFemales>,<maxFemales>)\n" + 
    "  Ants(<minDrones>,<maxDrones>)\nDefault: '-m Meme'\n" +
    "Examples: '-m Duke', '-m Fish(7,15)', '-m Ants(10,20)'",
    "Meme", false,
    """(Meme)|(Duke)|(Fish\([0-9]+,[0-9]+\))|(Ants\([0-9]+,[0-9]+\))"""
  ),
  new ArgsOption(List("--exp-1-cdf"), 
    "Outputs values of distribution function of Exp_1 in the first column.",
    "false", true
  ),
  new ArgsOption(List("--mrca-ecdf"), 
    "Output values of empirical cumulative distribution \n" +
    "function of the MRCA time. One column per pedigree is produced. ",
    "false", true
  ),
  new ArgsOption(List("--mrca-avg"),
    "Output average MRCA time (one for each pedigree)", "false", true
  ),
  new ArgsOption(List("--verbose","-v"), 
    "Generates verbose output.", "false", true),
  new ArgsOption(List("--show-environment"),
    "Dumps first 'g' populations and parent family choices.\n" +
    "Works only in verbose mode.\n" +
    "It's preferable to set '-p 1' on multicore machines, otherwise the \n" +
    "output for different pedigrees can get scrambled.\n" +
    "Don't use it with large 'N'.\n" +
    "Default: '--show-environment 0'\n" +
    "Example: '--show-environment 20' shows first 20 generations",
    "0", false, "[1-9][0-9]*"),
  new ArgsOption(List("--track-progress"),
    "Prints progress information to STDERR.\n" +
    "Looks really cool with multi-core CPU's.", "false", true),
  new ArgsOption(List("--comment"), 
    "Prepends the specified prefix to each line of verbose output.\n" +
    "Try '--comment \"#\"' for gnuplot or '--comment \"%\"' for LaTeX",
    "%", false, ".+"
  ),
  new ArgsOption(List("--plot-resolution"),
    "Step width for ECDF plots. Default: '--plot-resolution 0.01'",
    "0.01",
    false,
    "[0-9]+(\\.[0-9]+)?"
  ),
  new ArgsOption(List("--plot-max"),
    "Step width for ECDF plots. Default: '--plot-max 3.0'",
    "3.0",
    false,
    "[0-9]+(\\.[0-9]+)?"
  ),
  new ArgsOption(List("--only-populations"),
    "Don't simulate any coalescents. Just generate the populations, \n" +
    "output intrinsic time and number of families (two columns).",
    "false",
    true
  ),
  createIndexOption
)).withHelp(
  "Simulates gene genealogies in fixed pedigrees.\n Available options are:",
  "\nA typical invocation might look as follows: \n\n" +
  "  scala coalescentSimulation.scala \\\n" +
  "  --sample-size 2 --num-families 100 --num-families-variation 0.75 \\\n" +
  "  --model 'Ants(5,10)' --pedigrees 20 --coalescents 1000  \\\n" +
  "  --verbose --comment '#' \\\n" +
  "  --exp-1-cdf --mrca-ecdf --track-progress\n\n" +
  "These settings describe a model with family structure of an ant colony\n" +
  "where a single queen and 5 to 10 males contribute to the genome of each\n" +
  "colony. \n" +
  "  The number of colonies in each generation varies between 25 and 175. \n" +
  "This command would generate 20 different pedigrees, and simulate 1000\n" +
  "coalescents on each pedigree. \n" +
  "Each coalescent would start with 2 active lineages.\n" +
  "  The program would output all the settings, prefixed by an '#'-symbol.\n" +
  "Then it would print a big table, with t-values in the first column, \n" +
  "CDF of Exp_1 in the second column, and then 20 further columns with \n" +
  "ECDF's of pair coalescence times (one column per pedigree)."
)

/* #############################################################################
   [!]                 Entry point, running the experiment
   ###########################################################################*/

val augmentedArgs = if (args.isEmpty) Array("--help") else args
cli.parse(augmentedArgs)

val verboseMode = cli("--verbose").toBoolean
val trackProgress = cli("--track-progress").toBoolean
val showEnvironment = cli("--show-environment").toInt
val commentPrefix = cli("--comment")
def printVerbose(s: String): Unit = if (verboseMode) {
  println(s.split("\n").map{l => commentPrefix + " " + l}.mkString("\n"))
}
def printProgress(s: String): Unit = if (trackProgress) {
  System.err.println(s)
}

// dump the settings if necessary
printVerbose(cli.verboseDescription)

val numFamilies = cli("--num-families").toInt
val variation = cli("--num-families-variation").toDouble
if (variation < 0.0 || variation >= 1.0) {
  println("Invalid --num-families-variation: " + variation + 
    " (expected 0 <= x < 1)")
  System.exit(1)
}
val plotMax = cli("--plot-max").toDouble

val numFamiliesProcess = if (variation == 0.0) {
  printVerbose("Number of families is constant " + numFamilies)
  new DeterministicFunction[Int] { def apply(t: Int) = numFamilies }
} else {
  val minFamilies = (numFamilies * (1 - variation)).toInt
  val maxFamilies = (numFamilies * (1 + variation)).toInt
  // 2.0 is to keep it crashing into walls frequently,
  // square root is to keep the relative variance roughly the same at all
  // time scales.
  val jumpSize = 2.0 * math.sqrt(numFamilies)
  printVerbose("Number of families is a bounded random walk \n" + 
    "with values between " + minFamilies + " and " + maxFamilies + "\n" +
    "making jumps of size " + jumpSize)
  (new BoundedRandomWalk(minFamilies, maxFamilies, jumpSize)).mapPointwise{
    _.toInt
  }
}

val familyStructure = {
  val model = cli("--model").trim
  if (model == "Meme") {
    printVerbose("Family structure: 'Meme', all families look the same.")
    MemeFamilyStructure
  } else if (model == "Duke") {
    printVerbose("Family structure: 'Duke', all families look the same.")
    DukeFamilyStructure
  } else if (model.startsWith("Fish") || model.startsWith("Ants")) {
    val modelName = model.take(4)
    val intParams = model.drop(5).dropRight(1).split(",").map(_.toInt)
    printVerbose(
      "Chosen model: '" + modelName + 
      "' with parameters: " + intParams.mkString(" ")
    )
    if (intParams.size != 2) {
      println("Expected 2 integer params, but got " + intParams.size)
      System.exit(1)
    }
    if (!intParams.forall{p => p >= 0 && p < 127}) {
      println("Invalid family model params: expected values between 0 and 126")
      System.exit(1)
    }
    val minOpp = intParams(0).toByte
    val maxOpp = intParams(1).toByte
    if (modelName == "Fish") {
      FishFamilyStructure(minOpp, maxOpp)
    } else if (modelName == "Ants") {
      AntsColonyStructure(minOpp, maxOpp)
    } else {
      throw new Exception(
        "Unrecognized parameterized model name: " + modelName)
    }
  } else {
    throw new Exception("Unrecognized model: " + model)
  }
}

val generationsProcess = randomPopulationHistory(
  numFamiliesProcess,
  familyStructure
)

val numPedigrees = cli("--pedigrees").toInt
val numCoalescents = cli("--coalescents").toInt
val sampleSize = cli("--sample-size").toInt

val statMrcaEcdf = cli("--mrca-ecdf").toBoolean
val statMrcaAvg = cli("--mrca-avg").toBoolean

// run experiment only if it's really required...
val simulateCoalescents = statMrcaEcdf || statMrcaAvg
val simulateOnlyPopulations = cli("--only-populations").toBoolean

if (simulateOnlyPopulations && simulateCoalescents) {
  println("No coalescents can be simulated when option --only-populations " +
    "is active. Please remove --mrca-ecdf, --mrca-avg and all other flags " +
    "that require simulation of coalescents."
  )
  System.exit(2)
}

// This is the main experiment: simulation of coalescents in fixed pedigrees
if (simulateCoalescents) {

  val experimentStartTime = System.currentTimeMillis
  val pedigreeProgress = new Array[Double](numPedigrees)
  var lastProgressDisplay = experimentStartTime
  def showPedigreeProgress(force: Boolean = false): Unit = {
    if (trackProgress) {
      val now = System.currentTimeMillis
      if (now - lastProgressDisplay > 250 || force) {
        lastProgressDisplay = now
        printProgress("Progress after " + (now - experimentStartTime) + " ms :")
        for (pIdx <- 0 until numPedigrees) {
          val percentageFloat = pedigreeProgress(pIdx) * 100
          val percentage = percentageFloat.toInt
          printProgress(
            "%4d ".format(pIdx) + ("#" * percentage) + 
            (" " * (100 - percentage)) + " " + 
            "%6.2f %%".format(percentageFloat)
          )
        }
      }
    }
  }

  // each pedigree can be treated completely independently -> parallelize
  val statsForAllPedigrees = for (pIdx <- (0 until numPedigrees).par) yield {
    var labeledStats: List[(String,Statistic[StatesHoldingTimes, _])] = Nil
    if (statMrcaEcdf) {
      labeledStats ::=
        ("--mrca-ecdf", (new EcdfStatistic()).prepend{ tree => tree.mrcaTime })
    }
    if (statMrcaAvg) {
      labeledStats ::= 
        ("--mrca-avg", (new RealAverage()).prepend{ tree => tree.mrcaTime })
    }
  
    val fixedGenerations = generationsProcess.sample

    val intrinsicTime = virtualTime(
      fixedGenerations,
      WrightFisherFactory,
      familyStructure
    )

    val fixedPedigree = 
      randomPedigree(fixedGenerations, WrightFisherFactory).sample

    if (showEnvironment > 0) {
      printVerbose("Random environment " + pIdx)
      printVerbose("Generations: ")
      for (exampleGen <- fixedGenerations.take(showEnvironment)) 
        printVerbose(exampleGen.toString)
      printVerbose("Pedigree: ")
      for (examplePfc <- fixedPedigree.take(showEnvironment)) 
        printVerbose(examplePfc.toString)
    }

    val coalescentFullLaw = partitionCoalescentHistory(
      sampleSize,
      fixedPedigree
    )
    val coalescentLaw = for (path <- coalescentFullLaw) yield {
      StatesHoldingTimes(sampleSize, path, intrinsicTime)
    }
    for (cIdx <- 0 until numCoalescents) {
      val coalescentRealization = coalescentLaw.sample
      for ((_,s) <- labeledStats) {
        s.consume(coalescentRealization)
      }
      pedigreeProgress(pIdx) =  (cIdx + 1) / numCoalescents.toDouble
      if (cIdx % 10 == 0) showPedigreeProgress() 
    }
    labeledStats
  }
  showPedigreeProgress(true)
  val experimentEndTime = System.currentTimeMillis
  val experimentTime = (experimentEndTime - experimentStartTime) / 1000.0
  
  printVerbose("Total time = %10.2f sec = %10.2f min".format(
    experimentTime, experimentTime / 60.0))

  // output results of the statistics
  val plotResolution = cli("--plot-resolution").toDouble
  if (plotResolution <= 0.0) {
    println("Non-positive plot resolution: " + plotResolution)
    System.exit(1)
  }
  
  val exp1cdf = cli("--exp-1-cdf").toBoolean
  def selectStats[Y](label: String): List[Statistic[StatesHoldingTimes,Y]] = {
    (for {
      labeledStats <- statsForAllPedigrees
      (statLabel, stat) <- labeledStats
      if (statLabel == label)
    } yield stat.asInstanceOf[Statistic[StatesHoldingTimes, Y]]).toList
  }
  
  if (statMrcaAvg) {
    printVerbose("Results --mrca-avg:")
    for (s <- selectStats("--mrca-avg")) {
      println(s.result)
    }
  }

  if (statMrcaEcdf) {
    printVerbose("Results --mrca-ecdf:")
    val ecdfs = selectStats[EmpiricalReal]("--mrca-ecdf").map{_.result}
    val numSteps = (plotMax / plotResolution).toInt
    for (k <- (0 to numSteps)) {
      val t = k * plotResolution
      printf("%2.6f ", t)
      if (exp1cdf) {
        printf("%2.6f ", 1 - math.exp(-t))
      }
      for (ecdf <- ecdfs) {
        printf("%2.6f ", ecdf.cdf(t))
      }
      println()
    }
  }
}

// Simulating only populations: printing 
// a columnt with virtual time, and a column with varying 
// number of families `(N_g)_g`.
if (simulateOnlyPopulations) {
  printVerbose("Results --only-populations " +
    "(intrinsic time, number of families):"
  )
  val fixedGenerations = generationsProcess.sample
  val intrinsicTime = virtualTime(
    fixedGenerations,
    WrightFisherFactory,
    familyStructure
  )
  for ((t,g) <- intrinsicTime zip fixedGenerations) {
    if (t > plotMax) {
      System.exit(0) // enough, just quit
    } else {
      printf("%2.6f %2.6f\n".format(t, g.numFamilies.toDouble / numFamilies))
    }
  }
}
