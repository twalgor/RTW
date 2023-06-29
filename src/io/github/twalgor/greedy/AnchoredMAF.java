package io.github.twalgor.greedy;

import io.github.twalgor.acsd.ACSDecomposition;
import io.github.twalgor.acsd.ACSDecomposition.MTAlg;
import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.MinimalizeTD;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.heap.Heap;
import io.github.twalgor.heap.Queueable;
import io.github.twalgor.log.Log;

public class AnchoredMAF {
//  static final boolean TRACE = true;
  static final boolean TRACE = false;
  Graph g;
  XBitSet anchor;
  int k;
  
  XBitSet[] nb;
  boolean anchorDone;

  Heap heap;

  int[] ord;
  int targetWidth;
  public int width;
  XBitSet removed;
  
  boolean debug;
  
  public int getWidth() {
    return width;
  }
  
  public Graph getGraph() {
    return g;
  }

  public AnchoredMAF(Graph g, XBitSet anchor, int k) {
    this.g = g;
    this.anchor = anchor;
    this.k = k;
    
    g.checkConsistency();
    assert g.isClique(anchor);
    assert g.neighborSet(g.all.subtract(anchor)).equals(anchor);
    assert k >= anchor.cardinality();
  }

  public TreeDecomposition decomposeMinimal() {
    TreeDecomposition td = decompose();
    return MinimalizeTD.minimalize(td);
  }
  
  public TreeDecomposition decompose() {
    Graph h = triangulate();
    TreeDecomposition td = Chordal.chordalToTD(h);
    td.g = g;
    return td;
  }
  
  public Graph triangulate() {
    if (TRACE) {
      System.out.println("g.n = " + g.n);
    }
    width = 0;
    order();
    Graph h = g.copy();
    XBitSet vs = (XBitSet) g.all.clone();
    
    for (int i = 0; i < g.n; i++) {
      int v= ord[i];
      assert nb[v].equals(h.neighborSet[v].intersectWith(vs));
      h.fill(nb[v]);
      vs.clear(v);
    }
    
//    verifyOrder(h, ord);
    return h;
  }
  
  void verifyOrder(Graph h, int[] ord) {
    XBitSet vs = (XBitSet) g.all.clone();
    for (int v: ord) {
      System.out.println("v " + v + " nb " + h.neighborSet[v].intersectWith(vs));
      assert h.isClique(h.neighborSet[v].intersectWith(vs));
      vs.clear(v);
    }
  }

  void order() {
    XBitSet remaining = (XBitSet) g.all.clone();
    heap = new Heap(g.n);
    anchorDone = false;

    nb = new XBitSet[g.n];
    Vertex[] vertex = new Vertex[g.n];
    for (int v = 0; v < g.n; v++) {
      nb[v] = (XBitSet) g.neighborSet[v].clone();
      vertex[v] = new Vertex(v);
    }
    
    for (int v = 0; v < g.n; v++) {
      vertex[v].evaluate();
      if (!anchor.get(v)) {
        heap.add(vertex[v]);
      }
    }
 
    ord = new int[g.n];


    while (!remaining.isEmpty()) {
      if (TRACE) {
        System.out.println(" remaining = " + remaining.cardinality());
      }

      if (debug) {
        System.out.println(remaining.cardinality() + " remaining out of " + g.n);
      }

      Vertex vMin = null;
      if (!anchorDone) {
        int v0 = -1;
        for (int v: anchor.toArray()) {
          if (v0 == -1 || nb[v].cardinality() <= nb[v0].cardinality()) {
            v0 = v;
          }
        }
        if (nb[v0].cardinality() <= k + 1) {
          if (TRACE) {
            System.out.println("v0 " + v0 + " chosen from anchor ");
          }
          vMin = vertex[v0];
          anchorDone = true;
          for (int v: anchor.toArray()) {
            if (v != v0) {
              vertex[v].evaluate();
              heap.add(vertex[v]);
            }
          }
        }
      }
      if (vMin == null) {
        vMin = (Vertex) heap.removeMin();
        if (TRACE) {
          System.out.println("vMin " + vMin.id + " from heap ");
        }

      }

      if (TRACE) {
        System.out.println("vMin = " + vMin + 
            ", nb = " + nb[vMin.id]);
      }
      
      if (nb[vMin.id].cardinality() > width) {
        //        System.out.println("vMin = " + vMin.id + ", cardinality = " + 
        //            + nb[vMin.id].cardinality());
        width = nb[vMin.id].cardinality();
      }

      ord[g.n - remaining.cardinality()] = vMin.id;

      fill(vMin.id);
      remaining.clear(vMin.id);

      for (int v : nb[vMin.id].toArray()) {
        assert !nb[v].get(vMin.id);
      }
      
      XBitSet affected = (XBitSet) nb[vMin.id].clone();

      for (int v : nb[vMin.id].toArray()) {
        XBitSet missing = nb[vMin.id].subtract(nb[v]);
        missing.clear(v);
        for (int w = missing.nextSetBit(v + 1); w >= 0; w = missing.nextSetBit(w + 1)) {
          nb[v].set(w);
          nb[w].set(v);
          affected.or(nb[v].intersectWith(nb[w]));
        }
      }

      assert nb[vMin.id].isSubset(remaining);

      for (int v = affected.nextSetBit(0); v >= 0;
          v = affected.nextSetBit(v + 1)) {
        if (anchorDone || !anchor.get(v)) {
          heap.remove(vertex[v]);
        }
      }
      for (int v = affected.nextSetBit(0); v >= 0;
          v = affected.nextSetBit(v + 1)) {
        vertex[v].evaluate();
      }
      for (int v = affected.nextSetBit(0); v >= 0;
          v = affected.nextSetBit(v + 1)) {
        if (anchorDone || !anchor.get(v)) {
          heap.add(vertex[v]);
        }
      }
    }
  }

  void fill(int w) {
    for (int v = nb[w].nextSetBit(0); v >= 0; v = nb[w].nextSetBit(v + 1)) {
      nb[v].or(nb[w]);
      nb[v].clear(w);
      nb[v].clear(v);
    }
  }

  class Vertex implements Queueable {
    int id;
    int degree;
    int nFill;
    int hx;

    Vertex(int id) {
      super();
      this.id = id;
    }

    void evaluate() {
      degree = nb[id].cardinality();
      nFill = 0;
      for (int v = nb[id].nextSetBit(0); v >= 0; v = nb[id].nextSetBit(v + 1)) {
        nFill += (nb[id].subtract(nb[v]).cardinality() - 1);
      }
      nFill /= 2;
    }

    @Override
    public int compareTo(Object x) {
      Vertex v = (Vertex) x;
      if (degree == 0 && v.degree != 0) {
        return -1;
      }
      if (v.degree == 0 && degree != 0) {
        return 1;
      }
      if (nFill * v.degree == v.nFill * degree) {
        return id - v.id;
      }
      return nFill * v.degree - v.nFill * degree;
    }

    @Override
    public boolean equals(Object o) {
      return compareTo((Vertex) o) == 0;
    }

    @Override
    public String toString() {
      return id + ":" + degree + "," + nFill;
    }

    @Override
    public void setHeapIndex(int i) {
      hx = i;
    }

    @Override
    public int getHeapIndex() {
      return hx;
    }
  }
  
  private static void test(String path, String name) {
    Log log = new Log("MMAF", name);

    Graph g = Graph.readGraph(path, name);
    // Graph g = Graph.readGraph("instance/" + path, name);

    log.log("Graph " + name + " read, n = " + g.n + ", m = " + g.numberOfEdges());

    ACSDecomposition acsd = new ACSDecomposition(g, MTAlg.mmaf);
    acsd.decomposeByACS();
    XBitSet largestAtom = null;
    for (XBitSet atom : acsd.acAtoms) {
      if (largestAtom == null || atom.cardinality() > largestAtom.cardinality()) {
        largestAtom = atom;
      }
    }

    log.log("Largest atom: " + largestAtom.cardinality());

    LocalGraph local = new LocalGraph(g, largestAtom);

    long t0 = System.currentTimeMillis();
    AnchoredMAF amaf = new AnchoredMAF(local.h, null, 0);
    amaf.triangulate();
    long t = System.currentTimeMillis();
    log.log("width " + amaf.width + ", "  + (t - t0) + " milliseces");
  }
  
  public static void main(String[] args) {
//  Graph g = Graph.readGraph(System.in);
    test("..\\instance\\PACE2017bonus_gr", "\\Promedus_12_14");
}

}
