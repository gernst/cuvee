package cuvee.util

/* 
  This is a Union-Find or Disjoint-Sets data structure.
  It can be used to represent a DAG (Directed-Acyclic-Graph) by
  mapping the node that points to another as key and value.

  Isn't the union inefficient as f***?
  https://en.wikipedia.org/wiki/Disjoint-set_data_structure

  TODO: find out whats called more often, find or union and then rework this so that the one called more often is O(1)
*/
class UnionFind[A](var parent: Map[A, A]) {
    
    def find_aux(a: A, parent0: Map[A, A]): (A, Map[A, A]) = {
        val b = parent0.getOrElse(a, a)
        if (b == a) {
            (a, parent0)
        } else {
            val (r, parent1) = find_aux(b, parent0)
            (r, parent1 + (a -> r))
        }
    }

    /* Returns the representative equivalence class which contains the element a   */
    def find(a: A): A = {
        val (r, parent1) = find_aux(a, parent)
        parent = parent1
        r
    }

    /* combines the 2 equivalence classes of a and b into one */
    def union(a1: A, a2: A): UnionFind[A] = {
        val r1 = find(a1)
        val r2 = find(a2)
        new UnionFind[A](parent + (r1 -> r2))
    }

    override def toString = {
        val m = parent.keys map { a => (find(a), a) }
        val g = m.groupBy(_._1).toList
        val gs = g map {
            case (r, c) => 
            c.map(_._2).mkString("{ " + r + "*, ", ", ", " }")
        }
        gs.mkString("\n")
    }

    def toMap = {
        var modelMap: Map[A, A] = Map()
        parent.keys.foreach(a => modelMap += (a -> find(a)))
        modelMap
    }
}

object UnionFind {
    def empty[A] = new UnionFind[A](Map.empty)
}