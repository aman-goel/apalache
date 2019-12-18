package at.forsyte.apalache.tla.bmcmt.search

import java.util.concurrent.atomic.AtomicLong

import at.forsyte.apalache.tla.lir.TlaEx


/**
  * The tree that is constructed in the course of the search. In this tree, a node is indexed by the sequence
  * of edge indices.
  *
  * @author Igor Konnov
  */
class HyperNode private(val id: Long, val transition: HyperTransition) extends Serializable {
  var depth: Int = 0

  var parent: Option[HyperNode] = None

  private var nodeChildren: Seq[HyperNode] = Seq()

  /**
    * Is the node explored? If true, the workers have to pick another node, e.g., one of the node's children.
    */
  var isExplored: Boolean = false

  /**
    * The status of the transitions that have to explored in this node.
    */
  var openTransitions: Map[Int, (TlaEx, TransitionStatus)] = Map()

  /**
    * The snapshot that is made after exploring the node.
    */
  var snapshot: Option[SearchSnapshot] = None

  /**
    * Get the node children
    * @return the list of children (may change after append)
    */
  def children: Seq[HyperNode] = nodeChildren

  /**
    * Append one more node to the end of the children list. This method sets the child's parent to this.
    * @param child new child
    */
  def append(child: HyperNode): Unit = {
    nodeChildren = nodeChildren :+ child
    child.parent = Some(this)
    child.depth = depth + 1
  }

  /**
    * Find a node from the current one by following the node's prefix, that is, the sequence of children indices
    * that leads to the node.
    * @return Some(node) for the found node, if the sequence leads to a node, and None otherwise
    */
  def findByPrefix: HyperNode.indexType => Option[HyperNode] = {
    case Nil => Some(this)
    case childIndex :: tail =>
      if (children.isDefinedAt(childIndex)) {
        children(childIndex).findByPrefix(tail)
      } else {
        None
      }
  }

  /**
    * Given a tree node, find the node's prefix from the root to the node.
    * @return node's prefix, that is, the sequence of indices leading from the root to the node.
    */
  def findPrefix: HyperNode.indexType = {
    parent match  {
      case None => Seq()
      case Some(p) => p.findPrefix :+ p.children.indexOf(this)
    }
  }

  def findPrefixAsString: String = {
    findPrefix.mkString(".")
  }
}

object HyperNode {
  private var nextId: AtomicLong = new AtomicLong()

  type indexType = Seq[Int]

  def apply(transition: HyperTransition, children: HyperNode*): HyperNode = {
    val id = nextId.getAndIncrement()
    val node = new HyperNode(id, transition)
    children.foreach(node.append)
    node
  }
}