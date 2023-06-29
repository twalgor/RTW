package io.github.twalgor.ulb;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.minseps.MinSepsGenerator;

public class MinSepsConstrained {
//  static final boolean TRACE = true;
  static boolean TRACE = false;
  Graph g;
  Graph constrainer;
  XBitSet aExcluded;
  public Set<XBitSet> minSeps;
  
  int aTarget;
  XBitSet aCompoTarget;
  XBitSet bCompoTarget;
    
  public MinSepsConstrained(Graph g, Graph constrainer) {
    this.g = g;
    this.constrainer = constrainer;

    if (TRACE) {
      System.out.println("MinSepsConstrained n = " + g.n + 
          " edges in g: " + g.numberOfEdges() + 
          " edges in constrainer " + constrainer.numberOfEdges());
    }
  }
  
  public void generate() {
    minSeps = new HashSet<>();

    aExcluded = new XBitSet(g.n);
    for (int a = 0; a < g.n; a++) {
      XBitSet aSide = new XBitSet(new int[] {a});
      XBitSet bSide = g.all.subtract(g.neighborSet[a]);
      bSide.clear(a);
      XBitSet sFixed = g.neighborSet[a].intersectWith(aExcluded);
      if (!constrainer.isClique(sFixed)) {
        continue;
      }
      generateFrom(a, aSide, bSide, g.neighborSet[a],  
          sFixed, aExcluded, "");
      aExcluded.set(a);
    }
  }

  void generateFrom(int a, XBitSet aSide, XBitSet rest, XBitSet separator, XBitSet sFixed,
      XBitSet aExcluded, String indent) {

    assert g.neighborSet(aSide).equals(separator);
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    g.listComponents(rest, separator, fulls, nonFulls);
    
    for (XBitSet full: fulls) {
      if (TRACE) {
        System.out.println(indent + "full" + full);
      }
      branch(a, aSide, full, separator, sFixed, aExcluded, indent);
    }
    
    for (XBitSet bCompo: nonFulls) {
      XBitSet sep = g.neighborSet(bCompo);
      if (!sFixed.isSubset(sep)) {
        continue;
      }
      XBitSet rest1 = g.all.subtract(bCompo);
      rest1.andNot(sep);
      ArrayList<XBitSet> compos = g.componentsOf(rest1);
      for (XBitSet c: compos) {
        if (c.get(a)) {
          if (!c.intersects(aExcluded)) {
            branch(a, c, bCompo, sep, sFixed, aExcluded, indent);
          }
          break;
        }
      }
    }
  }
  
  void branch(int a, XBitSet aSide, XBitSet bSide, XBitSet separator, 
      XBitSet sFixed, XBitSet aExcluded,       
      String indent) {
    if (TRACE) {
      System.out.println(indent + "branch for a = " + a + 
          ", aSide = " + aSide);
      System.out.println(indent + "bSide = " + bSide);
      System.out.println(indent + "separator = " + separator);
      System.out.println(indent + "sFixed = " + sFixed);

      System.out.println(indent + minSeps.size() + " minSeps so far");
    }

    int nA = aSide.cardinality();
    int nS = separator.cardinality();
    if (nA * 2 + nS > g.n) {
      return;
    }

    assert sFixed.isSubset(separator);
    assert constrainer.isClique(sFixed);
    assert g.neighborSet(aSide).equals(separator);
    assert g.neighborSet(bSide).equals(separator);
    if (TRACE) {
      System.out.println(indent + "sFixed " + sFixed);
    }

    if (sFixed.equals(separator)) {
      minSeps.add(sFixed);
      return;
    }
    
    XBitSet toDecide = separator.subtract(sFixed);
    assert !toDecide.intersects(aExcluded);
    
    if (TRACE) {
      System.out.println(indent + "toDecide " + toDecide);
    }

    assert !toDecide.isEmpty();
    
//    if (sterile(aSide, bSide, separator, sFixed)) {
//      return;    
//    }
    
    int v = toDecide.nextSetBit(0);
    if (TRACE) {
      System.out.println(indent + "branching on " + v);
    }
    XBitSet rest = bSide.subtract(g.neighborSet[v]);
    XBitSet nb = g.neighborSet[v].subtract(separator);
    nb.andNot(aSide);
    XBitSet separator1 = separator.removeBit(v).unionWith(nb);
    XBitSet sFixed1 = sFixed.unionWith(nb.intersectWith(aExcluded));
    if (TRACE) {
      System.out.println(indent + "sFixed1 = " + sFixed1);
    }
    if (constrainer.isClique(sFixed1)) {
      generateFrom(a, aSide.addBit(v), rest, 
        separator1, sFixed1, aExcluded, indent + " ");
    }
    if (constrainer.isClique(sFixed.addBit(v))) {
      branch(a, aSide, bSide, separator, sFixed.addBit(v), aExcluded, indent + " ");
    }
  }
  
  int largestNeighborhoodVertex(XBitSet toDecide, XBitSet bSide) {
    int vLargest = toDecide.nextSetBit(0);
    assert vLargest >= 0;
    int sLargest = g.neighborSet[vLargest].intersectWith(bSide).cardinality();
    for (int v = toDecide.nextSetBit(vLargest); v >= 0; v = toDecide.nextSetBit(v + 1)) {
      int sN = g.neighborSet[v].intersectWith(bSide).cardinality(); 
      if (sN > sLargest) {
        vLargest = v;
        sLargest = sN;
      }
    }
    return vLargest;
  }
  
  static void test(String group, String name) {
    File file = new File("../instance/" + group + "/" + name + ".gr");
    Graph g = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g.n + ",  m =" + g.numberOfEdges());

    Random random = new Random(1);
    Minor minor = new Minor(g);
    Graph h = g;
    for (int i = 0; i < g.n / 3; i++) {
      int u = random.nextInt(h.n);
      int v = h.neighborSet[u].nextSetBit(0);
      minor = minor.contract(u, v);
      h = minor.getGraph();
    }
    
    Graph f = g.copy();
    MMAF mmaf = new MMAF(f);
    mmaf.triangulate();
    Chordal chordal = new Chordal(f);
    System.out.println("width " + mmaf.width);
    
    System.out.println("h.n " + h.n + " h.m " + h.numberOfEdges());
    Graph cg = h.copy();
    for (XBitSet pmc: chordal.maximalCliques()) {
      cg.fill(pmc.convert(minor.map));
    }
    
    MinSepsConstrained msc = new MinSepsConstrained(h, cg);
    msc.generate();
    Set<XBitSet> minSeps = msc.minSeps;
    System.out.println(minSeps.size() + " constrained minSeps");
    int k = XBitSet.largest(minSeps).cardinality();
    System.out.println("k " + k);
    MinSepsGenerator msg = new MinSepsGenerator(h, k);
    msg.generate();
    System.out.println(msg.minSeps.size() + " minSeps");
    for (XBitSet ms: msg.minSeps) {
      if (cg.isClique(ms)) {
        System.out.println(ms + " " + minSeps.contains(ms));
        assert minSeps.contains(ms);
      }
      
    }
  }
   
  
  public static void main(String[] args) {
//  test("grid", "troidal4_4");
//  test("grid", "troidal5_5");
//    test("grid", "troidal6_6");
//    test("grid", "troidal7_7");
//    test("pace17exact", "ex013");
//    test("pace17exact", "ex015");
//    test("pace17exact", "ex020");
//    test("pace17exact", "ex022");
//    test("pace17exact", "ex023");
//    test("pace17exact", "ex024");
//    test("pace17exact", "ex025");
//    test("pace17exact", "ex026");
//    test("pace17exact", "ex027");
//    test("pace17exact", "ex028");
//    test("pace17exact", "ex029");
    test("pace17exact", "ex030");
  }
 }

