package io.github.twalgor.decomposer;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.minseps.MinSepsGenerator;
import io.github.twalgor.sieve.SubblockSieve;

public class SemiPIDFull {
  static final int LINE_LENGTH =50;
//  static final boolean VALIDATE = true;
  static final boolean VALIDATE = false;
//  static final boolean CONSTRUCT_TD = true;
//static final boolean CONSTRUCT_TD = false;
//  static final boolean VERBOSE = true;
  static final boolean VERBOSE = false;
//  static final boolean TRACE = true;
  static boolean TRACE = false;
//  static final boolean TRACE_ROOT = true;
  static final boolean TRACE_ROOT = false;

  static final boolean CONSTRUCT_TD = false;
  
  Graph g;
  String graphName;
  int k;
  public Set<XBitSet> minSeps;
  boolean pmcOnly;
  Map<XBitSet, XBitSet> feasiblesMap;
  ArrayList<XBitSet> minSeparateds;
  
  SubblockSieve[] sieve;
  public Set<XBitSet> safeSeps;

  public SemiPIDFull(Graph g, int k) {
    this.g = g;
    this.k = k;
    MinSepsGenerator msg = new MinSepsGenerator(g, k);
    msg.generate();
    minSeps = msg.minSeps;
  }
  
  public SemiPIDFull(Graph g, int k, Set<XBitSet> minSeps) {
    this.g = g;
    this.k = k;
    this.minSeps = minSeps;
  }
  
  public void computeSafeSeps() {
    safeSeps = new HashSet<>();
    if (k >= g.n - 1) {
      return;
    }
    
    dp();

    for (XBitSet sep: minSeps) {
      if (isAllFeasible(sep)) {
//        System.out.println("all feasible " + sep);
        ArrayList<XBitSet> components = g.separatedComponents(sep);
//        System.out.println(components.size() + " components");
//        for (XBitSet compo: components) {
//          System.out.println(" " + compo);
//          System.out.println("  " + feasiblesMap.get(compo));
//        }
        safeSeps.add(sep);
      }
    }
    return;
  }
  
  public Set<XBitSet> capsOfFeasibles() {
    assert feasiblesMap != null;
    Set<XBitSet> result = new HashSet<>();
    result.addAll(feasiblesMap.values());
    return result;
  }

  public void dp() {
    minSeparateds = new ArrayList<>();
    
    for (XBitSet sep: minSeps) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      for (XBitSet full: fulls) {
        minSeparateds.add(full);
      }
    }

    minSeparateds.sort(XBitSet.cardinalityComparator);
    
    feasiblesMap = new HashMap<>();

    sieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      sieve[v] = new SubblockSieve(g, k + 1);
    }

    for (XBitSet component: minSeparateds) {
      XBitSet sep = g.neighborSet(component);
      XBitSet cap = findCap(component, sep, null);
      if (cap != null) {
        if (TRACE) {
          System.out.println(indent(component) + 
                "block: " + component);
        }
        feasiblesMap.put(component, cap);
        sieve[component.nextSetBit(0)].add(component, sep);
      }
    }
  }
  
  boolean isAllFeasible(XBitSet cap) {
    ArrayList<XBitSet> components = g.componentsOf(g.all.subtract(cap));
    for (XBitSet compo: components) {
      if (feasiblesMap.get(compo) == null) {
        return false;
      }
    }
    return true;
  }

  XBitSet findCap(XBitSet component, XBitSet sep, XBitSet knownCap) {
    if (TRACE || knownCap != null && sep.isSubset(knownCap)) {
      System.out.println(indent(component) + "findCap " + component + ", " + sep);
      if (knownCap != null) {
        System.out.println(indent(component) + "knownCap is " + knownCap);
      }
    }
    if (component.cardinality() + sep.cardinality() <= k + 1 &&
        g.isClique(component)) {
      return component.unionWith(sep);
    }
    int v0 = component.nextSetBit(0);

    ArrayList<XBitSet> candidates = sieve[v0].get(component, sep);
    for (XBitSet cand: candidates) {
      XBitSet candSep = g.neighborSet(cand);
      if (TRACE || knownCap != null && sep.isSubset(knownCap)) {
        System.out.println(indent(component) + "cand = " + cand + ", candSep = " + candSep);
      }
      if (sep.isSubset(candSep)) {
        if (otherFullsAllFeasible(candSep, cand, component)) {
          return candSep;  
        }
        else {
          continue;
        }
      }
      XBitSet union = sep.unionWith(candSep);
      assert !union.equals(sep);
      assert union.cardinality() <= k + 1;
      XBitSet cap = tryUnion(component.subtract(cand).subtract(union), union, knownCap);
      if (TRACE || knownCap != null && sep.isSubset(knownCap)) {
        System.out.println(indent(component) + "cap = " + cap);
      }
      if (cap != null) {
        return cap;
      }
    }
    if (TRACE || knownCap != null && sep.isSubset(knownCap)) {
      System.out.println(indent(component) + "try adding " + v0 + " to the bag");
    }
    return tryUnion(component.removeBit(v0), sep.addBit(v0), knownCap);
  }

  boolean  otherFullsAllFeasible(XBitSet candSep, XBitSet cand, XBitSet component) {
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    g.listComponents(component.subtract(cand).subtract(candSep), candSep, fulls, nonFulls);
    for (XBitSet full: fulls) {
//      System.out.println("full " + full + " examined");
      if (feasiblesMap.get(full) == null) {
        return false;
      }
    }
    return true;
  }

  XBitSet tryUnion(XBitSet scope, XBitSet union, XBitSet knownCap) {
    if (TRACE || knownCap != null && union.isSubset(knownCap)) {
      System.out.println(indent(scope) + "tryUnion0 " + 
          scope + ", " + union);
    }
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    g.listComponents(scope, union, fulls, nonFulls);
    for (XBitSet compo: nonFulls) {
      if (feasiblesMap.get(compo) == null) {
        if (TRACE || knownCap != null && union.isSubset(knownCap)) {
          System.out.println(indent(scope) + "infeasible, returninig null, compo = " + compo);
        }
        return null;
      }
    }
    if (fulls.isEmpty()) {
      if (TRACE) {
        System.out.println(indent(scope) + "no fulls, returninig " + 
            union);
      }
      if (!pmcOnly || g.isCliquish(union)) {
        return union;
      }
      else {
        return null;
      }
    }
    if (fulls.size() >= 2) {
      for (XBitSet full: fulls) {
        if (feasiblesMap.get(full) == null) {
          if (TRACE) {
            System.out.println(indent(scope) + 
                "infeasible full in at leaste two fulls, returninig null");
          }
          return null;
        }
      }
      if (TRACE) {
        System.out.println(indent(scope) + 
            "at least two fulls, all feasible, returninig " + union);
      }
      return union;
    }
    if (union.cardinality() == k + 1) {
      if (TRACE) {
        System.out.println(indent(scope) + 
            "no room for extending, returninig null");
      }
      return null;
    }
    assert fulls.size() == 1;
    XBitSet full = fulls.get(0);
    return findCap(full, union, knownCap);
  }

  int fillTD(XBitSet bag, XBitSet component, TreeDecomposition td) {
    if (CONSTRUCT_TD) {
      System.out.println("bag = " + bag);
      System.out.println(" component = " + component);
    }
    int r = td.addBag(bag.toArray());
    if (bag.cardinality() > td.width + 1) {
      td.width = bag.cardinality() - 1;
    }
    ArrayList<XBitSet> components = g.componentsOf(component.subtract(bag));
    for (XBitSet compo: components) {
      XBitSet cap = feasiblesMap.get(compo);
      assert cap != null:"compo = " + compo + 
          "\nsep = " + g.neighborSet(compo) + 
          "\nbag = " + bag;
      int b = fillTD(cap, compo, td);
      td.addEdge(r, b);
    }
    return r;
  }
  
  String indent(XBitSet compo) {
    return spaces((g.n - compo.cardinality()) * LINE_LENGTH / g.n);
  }
  
  static String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }
  
  static void test1(String group, String name, int width) {
    File file = new File("instance" + File.separator + group + File.separator + name + ".gr");
    Graph g = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g.n + ",  m =" + g.numberOfEdges());

    for (int k = width - 1; k <= width; k++) {
      System.out.println("trying width " + k);
      long t0 = System.currentTimeMillis();
      SemiPIDFull spid = new SemiPIDFull(g, k);
      spid.computeSafeSeps();
      if (spid.safeSeps.isEmpty()) {
       System.out.println("infeasible with " + spid.minSeps.size() + " min seps in " +
           (System.currentTimeMillis() - t0) + " millisecs");
      }
          
      else {
        System.out.println(spid.safeSeps.size() + " safe separators with " + 
            spid.minSeps.size() + " min seps in " +
            (System.currentTimeMillis() - t0) + " millisecs");
      }    
    }
  }

  public static void main(String[] args) {
    
//    test1("tw_uplow", "grid", "troidal3_3", 5);
//    test1("tw_uplow", "grid", "troidal4_4", 6);
//    test1("tw_uplow", "grid", "troidal5_5", 9);
//    test1("tw_uplow", "grid", "troidal6_6", 11);
//  test("coloring", "le450_5b");
//  test("coloring", "le450_5c");
//  test("coloring", "le450_5d");
//  test("coloring", "le450_15a");
//  test("coloring", "le450_15b");
//  test("coloring", "le450_15c");
//  test("coloring", "le450_15d");
//    test("coloring", "DSJC125.1");
//    test("coloring", "DSJC125.5");
//    test("coloring", "DSJC125.9");
//  test("coloring", "DSJC250.1");
//  test("coloring", "DSJC250.5");
//  test("coloring", "DSJC250.9");
//    test("coloring", "DSJC500.1");
//  test("coloring", "DSJC500.5");
//  test("coloring", "DSJC500.9");
//  test("coloring", "DSJC1000.1");
//test("coloring", "DSJC1000.5");
//test("coloring", "DSJC1000.9");
//    test("coloring", "DSJR500.5");
//    test("coloring", "homer");
//    test("coloring", "huck");
//    test("coloring", "games120");
//    test1("tw_uplow", "coloring", "queen7_7");
//    test1("tw_uplow", "coloring", "queen8_8");
//    test1("tw_uplow", "coloring", "queen9_9");
//    test1("tw_uplow", "coloring", "queen10_10");
//  test3("simplePMC", "coloring", "queen10_10", 72);
//  test3("simplePMC", "coloring", "queen11_11", 87);
//    test(11, 16);
//        test(20, 22);
//    test(20, 30);
//    test(30, 60);
//    test1("tw_uplow", "random", "gnm_040_120_1");
  test1("random", "gnm_050_150_1", 16);
//  test1("tw_uplow", "random", "gnm_050_150_1", 17);
//    test1("tw_uplow", "random", "gnm_050_200_1", 20);
//  test1("tw_uplow", "random", "gnm_050_250_1", 24);
//  test1("tw_uplow", "random", "gnm_050_300_1", 26);
//  test1("tw_uplow", "random", "gnm_050_350_1", 29);
//  test1("tw_uplow", "random", "gnm_050_400_1", 31);
//    test1("tw_uplow", "random", "gnm_060_180_1", 18);
//    test1("tw_uplow", "random", "gnm_060_240_1", 22);
//    test1("tw_uplow", "random", "gnm_060_300_1", 27);
//    test1("tw_uplow", "random", "gnm_060_360_1", 30);
//    test1("tw_uplow", "random", "gnm_060_420_1", 33);
//    test1("integratedTW", "random", "gnm_070_210_1", 22);
//    test3("tw_uplow", "random", "gnm_070_210_1", 22);
//    test1("tw_uplow", "random", "gnm_070_280_1", 28);
//    test1("tw_uplow", "random", "gnm_070_280_1", 29);
//    test1("tw_uplow", "random", "gnm_080_240_1", 25);
//    test1("tw_uplow", "random", "gnm_090_270_1", 27);
//  test1("tw_uplow", "random", "gnm_090_360_1", 35);
//  test3("simplePMC", "random", "gnm_050_150_1", 16);
//  test3("simplePMC", "random", "gnm_090_360_1", 33);
//  test1("tw_uplow", "random", "gnm_090_450_1", 40);
//    test("random", "gnm_090_450_1");
//    test("random", "gnm_090_540_1");
//    test("random", "gnm_100_300_1");
//    test("random", "gnm_100_400_1");
//    test("random", "gnm_100_500_1");
//    test("random", "gnm_100_600_1");
//    test("random", "gnm_100_700_1");
//    test("random", "gnm_100_800_1");
//    test("random", "gnm_100_900_1");
//    test("random", "gnm_100_1000_1");
//    test1("tw_uplow", "he2017secret", "he012");
//    test1("tw_uplow", "he2017secret", "he014");
//    test("he2017secret", "he014");
//    test1("tw_tripod", "pace17exact", "ex001", 10);
//    test3("integratedTW", "pace17exact", "ex003", 44);
//    test1("tw_tripod", "pace17exact", "ex001", 10);
//    test3("integratedTW", "pace17exact", "ex002", 19);
//    test1("tw_tripod", "pace17exact", "ex014", 18);
//    test3("integratedTW", "pace17exact", "ex181", 18);
//    test3("simplePMC", "ex2017bonus", "bonus-ex002", 19);
//    test("he2017secret", "he026");
//    test("he2017secret", "he104");
//    test("he2017secret", "he122");
//    test("he2017secret", "he124");
//    test("he2017secret", "he132");
//    test("he2017secret", "he150");
//    test("he2017secret", "he140");
//    test("he2017secret", "he154");
//    test("he2017secret", "he162");
  }
}

