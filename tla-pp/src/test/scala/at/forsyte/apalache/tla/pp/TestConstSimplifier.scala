package at.forsyte.apalache.tla.pp

import org.junit.runner.RunWith
import org.scalacheck.Prop.{AnyOperators, forAll, passed}
import org.scalacheck.Properties
import org.scalacheck.Gen
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.typecheck._

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker

/**
 * Tests for ConstSimplifier.
 */
@RunWith(classOf[JUnitRunner])
class TestConstSimplifier extends FunSuite with BeforeAndAfterEach with Checkers {
  private var simplifier: ConstSimplifier = _

  override def beforeEach(): Unit = {
    simplifier = new ConstSimplifier(new IdleTracker())
  }

  test("simplifies sums") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.plus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a + b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies sums with zeroes") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 2
    }
    val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expression = tla.plus(tla.int(0), ex) as IntT1()
      val result = simplifier.simplify(expression)
      val expected = simplifier.simplify(ex)

      result == expected
    }
    check(prop, minSuccessful(250), sizeRange(8))
  }

  test("simplifies subtractions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.minus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a - b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies subtractions that result in 0") {
    val prop = forAll { (a: BigInt) =>
      val expression = tla.minus(tla.int(a), tla.int(a)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == 0
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies multiplications") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mult(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a * b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies divisions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      if (b == 0) {
        true
      } else {
        val expression = tla.div(tla.int(a), tla.int(b)) as IntT1()
        val result = simplifier.simplify(expression)

        result match {
          case ValEx(TlaInt(x)) =>
            x == a / b
          case _ =>
            false
        }
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies mods") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      if (b == 0) {
        true
      } else {
        val expression = tla.mod(tla.int(a), tla.int(b)) as IntT1()
        val result = simplifier.simplify(expression)

        result match {
          case ValEx(TlaInt(x)) =>
            x == a % b
          case _ =>
            false
        }
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  // test("simplifies expoents") {
  //   val prop = forAll(posNum[BigInt]) { (a: BigInt, b: BigInt) =>
  //     val expression = tla.exp(tla.int(a), tla.int(b)) as IntT1()
  //     val result = simplifier.simplify(expression)

  //     result match {
  //       case ValEx(TlaInt(x)) =>
  //         x == a.pow(b.toInt)
  //       case _ =>
  //         false
  //     }
  //   }
  //   check(prop, minSuccessful(2), sizeRange(8))
  // }

}
