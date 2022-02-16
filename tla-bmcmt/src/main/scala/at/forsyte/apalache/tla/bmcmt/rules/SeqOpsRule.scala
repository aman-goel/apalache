package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, DefaultValueFactory, ProtoSeqOps}
import at.forsyte.apalache.tla.bmcmt.types.{CellT, IntT}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper
import at.forsyte.apalache.tla.lir._

/**
 * Sequence operations: Head, Tail, Len, SubSeq, Append, Concat.
 *
 * @author
 *   Igor Konnov
 */
class SeqOpsRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)
  private val proto = new ProtoSeqOps(rewriter)
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSeqOper.head, _)         => true
      case OperEx(TlaSeqOper.tail, _)         => true
      case OperEx(TlaSeqOper.subseq, _, _, _) => true
      case OperEx(TlaSeqOper.len, _)          => true
      case OperEx(TlaSeqOper.append, _, _)    => true
      case OperEx(TlaSeqOper.concat, _, _)    => true
      // TlaSeqOper.selectseq => ???
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaSeqOper.head, seqEx) =>
        val elemType = TlaType1.fromTypeTag(ex.typeTag)
        translateHead(state, seqEx, elemType)

      case OperEx(TlaSeqOper.len, seq) =>
        translateLen(state, seq)

      case OperEx(TlaSeqOper.tail, seq) =>
        translateTail(state, seq)

      case OperEx(TlaSeqOper.subseq, seq, newStart, newEnd) =>
        translateSubSeq(state, seq, newStart, newEnd)

      case OperEx(TlaSeqOper.append, seq, newElem) =>
        translateAppend(state, seq, newElem)

      case OperEx(TlaSeqOper.concat, seq, otherSeq) =>
        translateConcat(state, seq, otherSeq)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  /**
   * Translate Len(s) which is canonically defined as:
   *
   * <pre> CHOOSE n \in Nat : DOMAIN s = 1..n </pre>
   */
  private def translateLen(state: SymbState, seq: TlaEx): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setRex(seq))
    val lenCell = proto.seqLen(nextState.arena, nextState.asCell)
    nextState.setRex(lenCell.toNameEx as IntT1())
  }

  /**
   * Translate Head(s) which is canonically defined as:
   *
   * <pre> Head(s) == s[1] </pre>
   */
  private def translateHead(state: SymbState, seqEx: TlaEx, elemType: TlaType1): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setRex(seqEx))
    val seq = nextState.asCell
    val protoSeq = proto.fromSeq(nextState.arena, seq)
    nextState.setRex(proto.at(nextState.arena, protoSeq, 1).toNameEx as elemType)
  }

  /**
   * Translate Tail(s) which is canonically defined as:
   *
   * <pre> Tail(s) == CASE s # << >> -> [ i \in 1..(Len(s)-1) |-> s[i+1] ] </pre>
   */
  private def translateTail(state: SymbState, seq: TlaEx): SymbState = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq))
    val seqCell = nextState.asCell
    val (protoSeq, len, capacity) = proto.unpackSeq(nextState.arena, seqCell)
    if (capacity <= 0) {
      // Tail(seq) is undefined when Len(seq) = 0.
      // Therefore, we return the sequence itself, which would probably result in a spurious counterexample.
      nextState.setRex(seqCell.toNameEx)
    } else {
      def shiftByOne(state: SymbState, indexBase1: Int): (SymbState, ArenaCell) = {
        val elem = proto.at(state.arena, protoSeq, indexBase1 + 1)
        (state, elem)
      }

      nextState = proto.make(nextState, capacity - 1, shiftByOne)
      val newProtoSeq = nextState.asCell
      // If Len(seq) = 0, then the new length is -1. This is fine, as Tail is undefined on empty sequences.
      val newLen = tla.minus(len.toNameEx as IntT1(), tla.int(1)) as IntT1()
      nextState = rewriter.rewriteUntilDone(nextState.setRex(newLen))
      proto.mkSeq(nextState, seq.typeTag.asTlaType1(), newProtoSeq, nextState.asCell)
    }
  }

  /**
   * Translate SubSeq(S, m, n), which is canonically defined as:
   *
   * <pre SubSeq(s, m, n) == [ i \in 1..(1+n-m) |-> s[i+m-1] ] </pre>
   */

  private def translateSubSeq(state: SymbState, seqEx: TlaEx, newStartEx: TlaEx, newEndEx: TlaEx): SymbState = {
    // rewrite seqEx, newStartEx, and newEndEx
    var nextState = rewriter.rewriteUntilDone(state.setRex(seqEx))
    val seqT = seqEx.typeTag.asTlaType1().asInstanceOf[SeqT1]
    val seqCell = nextState.asCell
    val (protoSeq, len, capacity) = proto.unpackSeq(nextState.arena, seqCell)

    nextState = rewriter.rewriteUntilDone(nextState.setRex(newStartEx))
    val newStartBase1 = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newEndEx))
    val newEndBase1 = nextState.asCell
    // Computing the new length is quite tricky, as the users may mess up both start and end.
    // We are trying to compensate for this. This is different from the behavior of TLC though.
    nextState = nextState.updateArena(_.appendCell(IntT()))
    val adjustedStart = nextState.arena.topCell

    def solverAssert: TlaEx => Unit = rewriter.solverContext.assertGroundExpr

    def asInt(cell: ArenaCell) = cell.toNameEx as IntT1()

    // adjustedStart = IF newStartBase1 > 0 THEN newStartBase1 ELSE 1
    solverAssert(tla.eql(asInt(adjustedStart),
        tla.ite(tla.gt(asInt(newStartBase1), tla.int(0)) as BoolT1(), asInt(newStartBase1),
            tla.int(1)) as IntT1()) as BoolT1())
    // adjustedEnd = IF newEndBase1 <= len THEN newEndBase1 ELSE len
    nextState = nextState.updateArena(_.appendCell(IntT()))
    val adjustedEnd = nextState.arena.topCell
    solverAssert(tla.eql(asInt(adjustedEnd),
        tla.ite(tla.le(asInt(newEndBase1), asInt(len)) as BoolT1(), asInt(newEndBase1),
            asInt(len)) as IntT1()) as BoolT1())

    nextState = defaultValueFactory.makeUpValue(nextState, CellT.fromType1(seqT.elem))
    val defaultValue = nextState.asCell

    def copy(state: SymbState, dstIndexBase1: Int): (SymbState, ArenaCell) = {
      // Blindly copy the element adjustedStart + (dstIndex - 1) into the position at dstIndex.
      // If srcIndexEx is out of bounds, then `get` returns a cell, which may result in a spurious counterexample.
      val srcIndexEx = tla.plus(adjustedStart.toNameEx as IntT1(), tla.int(dstIndexBase1 - 1)) as IntT1()
      val newState = proto.get(picker, state, defaultValue, protoSeq, srcIndexEx)
      (newState, newState.asCell)
    }

    // Create the proto sequence of the same capacity, which is the worst case scenario.
    nextState = proto.make(nextState, capacity, copy)
    val newProtoSeq = nextState.asCell

    // newLen = IF adjustedEnd >= adjustedStart THEN 1 + adjustedEnd - adjustedStart ELSE 0
    nextState = nextState.updateArena(_.appendCell(IntT()))
    val newLen = nextState.arena.topCell
    solverAssert(tla.eql(asInt(newLen),
        tla.ite(tla.ge(asInt(adjustedEnd), asInt(adjustedStart)) as BoolT1(),
            tla.plus(tla.int(1), tla.minus(asInt(adjustedEnd), asInt(adjustedStart)) as IntT1()) as IntT1(),
            tla.int(0)) as IntT1()) as BoolT1())
    proto.mkSeq(nextState, seqEx.typeTag.asTlaType1(), newProtoSeq, newLen)
  }

  /**
   * Translate Append(s, e) which is canonically defined as:
   *
   * <pre> Append(s, e) == s \o << e >> </pre>
   */
  private def translateAppend(state: SymbState, seqEx: TlaEx, newElemEx: TlaEx): SymbState = {
    // rewrite seqEx and newElemEx
    var nextState = rewriter.rewriteUntilDone(state.setRex(seqEx))
    val seqCell = nextState.asCell
    val (protoSeq, len, capacity) = proto.unpackSeq(nextState.arena, seqCell)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newElemEx))
    val elemToAdd = nextState.asCell

    def pick(state: SymbState, dstIndexBase1: Int): (SymbState, ArenaCell) = {
      // Since we do not know the actual length of the sequence,
      // we have to pick the value at every position, except the last one.
      if (dstIndexBase1 > capacity) {
        // the last element is for sure equal to newElem (if lenCell == capacity)
        (state, elemToAdd)
      } else {
        // for all other elements, we pick either the element in the ith position, or the new element
        val seqElem = proto.at(state.arena, protoSeq, dstIndexBase1)
        val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(state, 2)
        val newState = picker
          .pickByOracle(oracleState, oracle, Seq(seqElem, elemToAdd), nextState.arena.cellTrue().toNameEx)
        val pickedCell = newState.asCell
        val cond = tla.le(tla.int(dstIndexBase1), len.toNameEx as IntT1()) as BoolT1()
        val when0 = oracle.whenEqualTo(nextState, 0)
        val ite = tla.ite(cond, when0, tla.not(when0) as BoolT1()) as BoolT1()
        rewriter.solverContext.assertGroundExpr(ite)
        (newState, pickedCell)
      }
    }

    // Create the proto sequence of capacity + 1, which is the worst case scenario.
    nextState = proto.make(nextState, capacity + 1, pick)
    val newProtoSeq = nextState.asCell
    // newLen = 1 + len
    val newLen = tla.plus(tla.int(1), len.toNameEx as IntT1()) as IntT1()
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newLen))
    proto.mkSeq(nextState, seqEx.typeTag.asTlaType1(), newProtoSeq, nextState.asCell)
  }

  /**
   * Translate concatenation of sequences, that is, s \o t, which is canonically defined as:
   *
   * <pre> s \o t == [ i \in 1..(Len(s) + Len(t)) |-> IF i \leq Len(s) THEN s[i] ELSE t[i-Len(s)] ] </pre>
   */
  private def translateConcat(state: SymbState, seq1ex: TlaEx, seq2ex: TlaEx): SymbState = {
    // rewrite seq1ex and seq2ex
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq1ex))
    val seq1 = nextState.asCell
    val seqT = seq1ex.typeTag.asTlaType1().asInstanceOf[SeqT1]
    val (protoSeq1, len1, capacity1) = proto.unpackSeq(nextState.arena, seq1)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(seq2ex))
    val seq2 = nextState.asCell
    val (protoSeq2, len2, capacity2) = proto.unpackSeq(nextState.arena, seq2)

    // we need the default value, when the sequences are empty
    nextState = defaultValueFactory.makeUpValue(nextState, CellT.fromType1(seqT.elem))
    val defaultValue = nextState.asCell

    def pick(state: SymbState, dstIndexBase1: Int): (SymbState, ArenaCell) = {
      if (dstIndexBase1 > capacity1) {
        // The index is beyond the capacity of the first sequence.
        // We only have to access the element of the second sequence with the index dstIndex - len1
        val indexEx = tla.minus(tla.int(dstIndexBase1), len1.toNameEx as IntT1()) as IntT1()
        val newState = proto.get(picker, state, defaultValue, protoSeq2, indexEx)
        (newState, newState.asCell)
      } else {
        // we access the element of the first sequence directly, with a constant index
        val elem1 = proto.at(state.arena, protoSeq1, dstIndexBase1)
        // we access the element of the second sequence indirectly,
        // as we cannot statically compute the length of the first sequence
        val indexEx2 = tla.minus(tla.int(dstIndexBase1), len1.toNameEx as IntT1()) as IntT1()
        var newState = proto.get(picker, state, defaultValue, protoSeq2, indexEx2)
        val elem2 = newState.asCell
        val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(newState, 2)
        newState = picker.pickByOracle(oracleState, oracle, Seq(elem1, elem2), nextState.arena.cellTrue().toNameEx)
        val pickedCell = newState.asCell
        val cond = tla.le(tla.int(dstIndexBase1), len1.toNameEx as IntT1()) as BoolT1()
        val when0 = oracle.whenEqualTo(nextState, 0) as BoolT1()
        val ite = tla.ite(cond, when0, tla.not(when0) as BoolT1()) as BoolT1()
        rewriter.solverContext.assertGroundExpr(ite)
        (newState, pickedCell)
      }
    }

    // Create the proto sequence of capacity = capacity1 + capacity2, which is the worst case scenario.
    nextState = proto.make(nextState, capacity1 + capacity2, pick)
    val newProtoSeq = nextState.asCell
    // newLen = len1 + len2
    val newLen = tla.plus(len1.toNameEx as IntT1(), len2.toNameEx as IntT1()) as IntT1()
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newLen))
    proto.mkSeq(nextState, seq1ex.typeTag.asTlaType1(), newProtoSeq, nextState.asCell)
  }
}
