package io.github.twalgor.acsd;

import java.util.ArrayList;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.heap.Heap;
import io.github.twalgor.heap.Queueable;

public class ContractionLB {
//  static final boolean TRACE = true;
  static final boolean TRACE = false;
  Graph g;
  Vertex[] vertex;
  XBitSet vertices;
  Minor minor;
  public Minor boundingMinor;

  public ContractionLB(Graph g) {
    this.g = g;
    minor = new Minor(g);
    vertex = new Vertex[g.n];
    for (int v = 0; v < g.n; v++) {
      vertex[v] = new Vertex(v, (XBitSet) g.neighborSet[v].clone());
    }
  }
  
  public int lowerbound() {
    if (TRACE) {
      System.out.println("lowerbounding n = " + g.n + ", m = " + g.numberOfEdges());
    }

    int lowerbound = 0;

    vertices = (XBitSet) g.all.clone();

    Heap heap = new Heap(vertices.cardinality());
    for (int i = vertices.nextSetBit(0); i >= 0; i = vertices.nextSetBit(i + 1)) {
      heap.add(vertex[i]);
    }
    
    while (!heap.isEmpty() && vertices.cardinality() > lowerbound + 1) {
      Vertex v0 = (Vertex) heap.removeMin();
      int deg = v0.nb.cardinality();
      if (deg > lowerbound) {
        lowerbound = deg;
        boundingMinor = minor;
      }
      ArrayList<Vertex> minDegVertices = new ArrayList<>();
      minDegVertices.add(v0);
      while (!heap.isEmpty()) {
        Vertex v = (Vertex) heap.removeMin();
        if (v.nb.cardinality() > deg) {
          heap.add(v);
          if (minDegVertices.size() == 1) {
            lowerbound = v.nb.cardinality();
            boundingMinor = minor;
          }
          break;
        }
        else {
          minDegVertices.add(v);
        }
      }
      
      if (deg == 0) {
        if (TRACE) {
          System.out.println("deg = " + deg + ", lowerbound = " + lowerbound);
        }
        for (Vertex v: minDegVertices) {
          vertices.clear(v.id);
        }
        continue;
      }
      
      Vertex best = v0;
      for (Vertex v: minDegVertices) {
        if (v.minCommon() < best.minCommon()) {
          best = v;
        }
      }
      for (Vertex v: minDegVertices) {
        if (v != best) {
          heap.add(v);
        }
      }
      if (TRACE) {
        System.out.println("vertices: " + vertices);
        System.out.println("heap size = " + heap.size());
      }
      int p = best.bestPartner();
      if (TRACE) {
        System.out.println("best = " + best.id + ", deg = " + deg + ", lowerbound = " + lowerbound + 
            ", best partner = " + p);
      }
      heap.remove(vertex[p]);

      XBitSet affected = best.nb.unionWith(vertex[p].nb);
      affected.clear(best.id);
      affected.clear(p);
      
      for (int w = affected.nextSetBit(0); w >= 0;
          w = affected.nextSetBit(w + 1)) {
        heap.remove(vertex[w]);
      }

      best.contractWith(p);
      
      for (int w = affected.nextSetBit(0); w >= 0;
          w = affected.nextSetBit(w + 1)) {
        heap.add(vertex[w]);
      }
      
      heap.add(best);
      
      for (int v = vertices.nextSetBit(0); v >= 0; v = vertices.nextSetBit(v + 1)) {
        assert vertex[v].nb.isSubset(vertices): v + ":" + vertex[v].nb + "\n" +
            vertex[v].nb.subtract(vertices);
      }
    }
    return lowerbound;
  }

  class Vertex implements Queueable{
    int id;
    XBitSet nb;
    int hx;
    
    Vertex (int id, XBitSet nb) {
      this.id = id;
      this.nb = nb;
    }

    int minCommon() {
      int min = nb.cardinality();
      for (int w = nb.nextSetBit(0); w >= 0; w = nb.nextSetBit(w + 1)) {
        if (nb.intersectWith(vertex[w].nb).cardinality() <
            min) {
          min = nb.intersectWith(vertex[w].nb).cardinality();
        }
      }
      return min;
    }
    
    int bestPartner() {
      int best = -1;
      for (int w = nb.nextSetBit(0); w >= 0; w = nb.nextSetBit(w + 1)) {
        if (best == -1 ||
            nb.intersectWith(vertex[w].nb).cardinality() <
            nb.intersectWith(vertex[best].nb).cardinality()) {
          best = w;
        }
      }
      return best;
    }
    
    void contractWith(int partner) {
      vertices.clear(partner);
      nb.or(vertex[partner].nb);
      for (int i = vertex[partner].nb.nextSetBit(0); 
          i >= 0; i = vertex[partner].nb.nextSetBit(i + 1)) {
        vertex[i].nb.clear(partner);
        vertex[i].nb.set(id);
      }
      nb.clear(id);
      assert !nb.get(partner);
      int u = minor.map[id];
      int v = minor.map[partner];
      minor = minor.contract(u, v);
    }
    
    @Override
    public int compareTo(Object x) {
      Vertex v = (Vertex) x;      if (nb.cardinality() != v.nb.cardinality()) { 
        return nb.cardinality() - v.nb.cardinality();
      }
      return id - v.id;  
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
  
  private static void test(String path, String name, int width) throws Exception{
    Graph g = Graph.readGraph("instance/" + path, name);
//    Graph g = Graph.readGraph("instance/" + path, name);

    System.out.println("Graph " + name + " read, n = " + 
        g.n + ", m = " + g.numberOfEdges() + ", width = " + width);
    // for (int v = 0; v < g.n; v++) {
    // System.out.println(v + ": " + g.degree[v] + ", " + g.neighborSet[v]);
    // }
    ContractionLB clb = new ContractionLB(g);
    int lb = clb.lowerbound();
    System.out.println("contraction lower bound: " + lb);
  }

  public static void main(String args[]) throws Exception {
//    test("pkt", "pkt_20_4_50_002", 4);
//    test("pkt", "pkt_20_4_60_001", 4);
//    test("pkt", "pkt_20_4_80_001", 4);
//    test("pkt", "pkt_30_4_40_004", 4);
//    test("pkt", "pkt_30_4_40_013", 4);
//    test("pkt", "pkt_30_4_50_001", 4);
//    test("pkt", "pkt_30_4_80_001", 4);
//    test("supercubic", "sc_15_023_1", 3);
//    test("supercubic", "sc_15_030_1", 5);
//    test("supercubic", "sc_20_030_1", 5);
//    test("supercubic", "sc_20_060_1", 8);
//    test("supercubic", "sc_40_060_1", 7);
//    test("supercubic", "sc_40_080_1", 9);
//    test("random", "gnm_070_210_1", 22);
//          test("random", "gnm_070_280_1");

//      test("random", "gnm_080_240_1");
    //  test("random", "gnm_080_320_1");
//      test("random", "gnm_090_270_1");
//      test("random", "gnm_090_360_1");
    //  test("random", "gnm_090_450_1");
//    test("pace17exact", "ex001", 10);
//    test("pace17exact", "ex002", 49);
//    test("pace17exact", "ex003", 44);
//    test("pace17exact", "ex004", 486);
//    test("pace17exact", "ex006", 7);
//  test("pace17exact", "ex007", 12);
//    test("pace17exact", "ex010", 9);
//    test("pace17exact", "ex014", 18);
//    test("pace17exact", "ex015", 15);
//    test("pace17exact", "ex019", 11);
//    test("pace17exact", "ex036", 119);
//    test("pace17exact", "ex038", 26);
//    test("pace17exact", "ex041", 9);
//    test("pace17exact", "ex048", 15);
//    test("pace17exact", "ex049", 13);
//    test("pace17exact", "ex050", 28);
//    test("pace17exact", "ex052", 9);
//    test("pace17exact", "ex053", 9);
//    test("pace17exact", "ex057", 117);
//    test("pace17exact", "ex059", 10);
//    test("pace17exact", "ex061", 22);
//    test("pace17exact", "ex063", 44);
    test("pace17exact", "ex064", 7);
//    test("pace17exact", "ex065", 25);
//    test("pace17exact", "ex066", 15);
//    test("pace17exact", "ex075", 8);
//    test("pace17exact", "ex081", 6);
//    test("pace17exact", "ex091", 9);
//    test("pace17exact", "ex095", 11);
//    test("pace17exact", "ex096", 9);
//    test("pace17exact", "ex100", 12);
//    test("pace17exact", "ex107", 12);
//    test("pace17exact", "ex121", 34);
//    test("pace17exact", "ex162", 9);
  }
}
