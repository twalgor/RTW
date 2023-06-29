package io.github.twalgor.common;

import java.util.HashSet;
import java.util.Set;

public class MinimalizeTD {
  static final String VERSION = "4";
  
  Graph g;
  Graph h;
  TreeDecomposition td;
  
  public static TreeDecomposition minimalize(TreeDecomposition td) {
    MinimalizeTD mtd = new MinimalizeTD(td.g, td);
    return mtd.minimalize();
  }
  
  public MinimalizeTD(Graph g, TreeDecomposition td) {
    this.g = g;
    this.td = td;
//    td.validate();
//    g.checkConsistency();
  }
  
  public TreeDecomposition minimalize() {
    h = g.copy();
    for (XBitSet bag: td.setOfBags()) {
      h.fill(bag);
    }

    Chordal chordal = new Chordal(h);
    XBitSet largest = XBitSet.largest(chordal.maximalCliques());
    assert largest.cardinality() <= td.width + 1: largest;
    chordal.order();
    int[] ord = chordal.ord;
    
    h = g.copy();
    triangulate(0, ord, (XBitSet) h.all.clone());
    assert h.isChordal();
    chordal = new Chordal(h);
    
    assert chordal.isMinimalTriangulationOf(g); 
    for (XBitSet clique: chordal.maximalCliques()) {
      if (!g.isPMC(clique)) {
        System.out.println("not pmc of g");
        System.out.println(clique);
        System.out.println(g.fullComponents(clique).size() + " full components");
        System.out.println("is cliquish " + g.isCliquish(clique));
      }
      assert g.isPMC(clique);
    }
    TreeDecomposition td1 = Chordal.chordalToTD(h);
    for (XBitSet bag: td1.setOfBags()) {
      assert g.isPMC(bag);
    }
    td1.g = g;
    assert td1.width <= td.width: td1.width + " " + td.width;
    return td1;
  }

  void triangulate(int i, int[] ord, XBitSet rem) {
    Subgraph sub0 = new Subgraph(h, rem);
    if (i == h.n - 1) {
      return;
    }
    int v0 = ord[i];

    Set<Edge> fills = new HashSet<>();
    //    XBitSet bag = new XBitSet(td.bags[b]).intersectWith(rem);
    XBitSet nb = h.neighborSet[v0].intersectWith(rem);
    assert nb.cardinality() <= td.width;
    for (int u : nb.toArray()) {
      for (int v : nb.toArray()) {
        if (v <= u) {
          continue;
        }
        if (!h.areAdjacent(u, v)) {
          Edge f = new Edge(u, v, h.n);
          fills.add(f);
        }
      }
    }
    for (Edge f: fills) {
      h.addEdge(f.u, f.v);
    }

    triangulate(i + 1, ord, rem.removeBit(v0));
    

    while (true) {
      Edge r = redundantFrom(fills, v0, rem, h);
      if (r == null) {
        break;
      }
      fills.remove(r);
      h.removeEdge(r.u, r.v);
    }
    Subgraph sub = new Subgraph(h, rem);
    assert sub.h.isChordal();
    Chordal chordal1 = new Chordal(sub.h);
    assert chordal1.isMinimalTriangulationOf(sub0.h);
  }

  Edge redundantFrom(Set<Edge> fills, int v0, XBitSet rem, Graph h) {
    for (Edge f: fills) {
      if (isRedundant(f, v0, rem, h)) {
        return f;
      }
    }
    return null;
  }

  boolean isRedundant(Edge f, int v0, XBitSet rem, Graph h) {
    XBitSet cn = h.neighborSet[f.u].intersectWith(h.neighborSet[f.v]);
    cn.and(rem);
    cn.clear(v0);
    if (!cn.isSubset(h.neighborSet[v0])) {
      return false;
    }
    for (int w = cn.nextSetBit(0); w >= 0; w = cn.nextSetBit(w + 1)) {
      for (int z = cn.nextSetBit(w + 1); z >= 0; z = cn.nextSetBit(z + 1)) {
        if (!h.areAdjacent(w, z)) {
          return false;
        }
      }
    }
    return true;
  }

  private XBitSet forgetVertices(int b, XBitSet inTree, XBitSet rem) {
    XBitSet fv = td.bagAt(b).intersectWith(rem);
    for (int b1: td.neighbor[b]) {
      if (inTree.get(b1)) {
        fv.andNot(td.bagAt(b1));
      }
    }
    return fv;
  }

  int leafOf(XBitSet inTree) {
    if (inTree.cardinality() == 1) {
      return inTree.nextSetBit(0);
    }
    for (int b = inTree.nextSetBit(0); b >= 0; b = inTree.nextSetBit(b + 1)) {
      XBitSet nb = new XBitSet(td.neighbor[b]).intersectWith(inTree);
      if (nb.cardinality() == 1) {
        return b;
      }
    }
    return 0;
  }
}
