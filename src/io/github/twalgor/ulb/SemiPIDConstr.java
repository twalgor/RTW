package io.github.twalgor.ulb;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.minseps.MinSepsGenerator;
import io.github.twalgor.sieve.SubblockSieve;

public class SemiPIDConstr {
  static final int LINE_LENGTH =50;
//  static final boolean VALIDATE = true;
  static final boolean VALIDATE = false;
//  static final boolean CONSTRUCT_TD = true;
static final boolean CONSTRUCT_TD = false;
//  static final boolean VERBOSE = true;
  static final boolean VERBOSE = false;
//  static final boolean TRACE = true;
  static boolean TRACE = false;

  
  Graph g;
  Graph cg;
  public int width;
  Set<XBitSet> minSeps;
  
  Map<XBitSet, XBitSet> feasiblesMap;
  ArrayList<XBitSet> minSeparateds;

  Map<XBitSet, Integer> widthMap;
  
  SubblockSieve[] sieve;

  public SemiPIDConstr(Graph g, Graph cg) {
    this.g = g;
    this.cg = cg;
    assert g.isConnected(g.all);
    if (VERBOSE) {
      System.out.println("n " + g.n + " g.m " + g.numberOfEdges() + " constraint.m " + cg.numberOfEdges());
    }
  }
  
  void debug() {
    MinSepsConstrained msc = new MinSepsConstrained(g, cg);
    msc.generate();
    minSeps = msc.minSeps;

    if (VERBOSE) {
      System.out.println(minSeps.size() + " minSeps");
    }
    minSeparateds = new ArrayList<>();
    
    for (XBitSet sep: minSeps) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      assert fulls.size() >= 2;
      for (XBitSet full: fulls) {
        minSeparateds.add(full);
      }
    }
    minSeparateds.add(g.all);

    minSeparateds.sort(XBitSet.cardinalityComparator);

    width = 36;
    
    dp();
    
    widthMap = new HashMap<>();
    
    for (XBitSet component: minSeparateds) { 
      XBitSet cap = feasiblesMap.get(component);
      if (cap != null) {
        int w = widthOf(component);
        widthMap.put(component, w);
      }
    }
    
    width = 35;
    dp();
  }
  
  int widthOf(XBitSet component) {
    XBitSet cap = feasiblesMap.get(component);
    assert cap != null;
    ArrayList<XBitSet> compos = g.separatedComponents(cap);
    int w = cap.cardinality() - 1;
    for (XBitSet c: compos) {
      if (!c.isSubset(component)) {
        continue;
      }
      Integer w1 = widthMap.get(c);
      assert w1 != null;
      if (w1 > w) {
        w = w1;
      }
    }
    return w;
  }
  
  public void decideWidth() {
    MinSepsConstrained msc = new MinSepsConstrained(g, cg);
    msc.generate();
    minSeps = msc.minSeps;
    
    if (VERBOSE) {
      System.out.println(minSeps.size() + " minSeps");
    }
    
//    Graph h = g.copy();
//    MMAF mmaf = new MMAF(h);
//    mmaf.triangulate();
//    
//    Chordal chordal = new Chordal(h);
//    for (XBitSet ms: chordal.minimalSeparators()) {
//      if (cg.isClique(ms)) {
//        System.out.println("constrained minsep " + ms);
//        System.out.println(" recognized " + minSeps.contains(ms));
//      }
//    }
    
    minSeparateds = new ArrayList<>();
    
    for (XBitSet sep: minSeps) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      assert fulls.size() >= 2;
      for (XBitSet full: fulls) {
        minSeparateds.add(full);
      }
    }
    minSeparateds.add(g.all);

    minSeparateds.sort(XBitSet.cardinalityComparator);
    
    for (width = g.minDegree(); width < g.n; width++) {
      dp();
      if (feasiblesMap.get(g.all) != null) {
        return;
      }
    }
  }
  
  void dp() {
    feasiblesMap = new HashMap<>();

    if (TRACE) {
      System.out.println("trying width " + width);
    }
    sieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      sieve[v] = new SubblockSieve(g, width + 1);
    }

    for (XBitSet component: minSeparateds) {
      XBitSet sep = g.neighborSet(component);
      if (sep.cardinality() > width) {
        continue;
      }
      XBitSet cap = feasiblesMap.get(component);
      if (cap != null) {
        sieve[component.nextSetBit(0)].add(component, cap);
        continue;
      }
      cap = findCap(component, sep);
      if (widthMap != null &&
          widthMap.get(component) != null &&
          widthMap.get(component) <= width) {
        assert cap != null: widthMap.get(component) + " " + component;
      }
      if (cap != null) {
//        if (cap.cardinality() == width + 1) {
//          System.out.println("*** tight cap " + cap);
//        }
        if (TRACE) {
          System.out.println(indent(component) + 
              "block: " + component);
        }
        feasiblesMap.put(component, cap);
        sieve[component.nextSetBit(0)].add(component, sep);
      }
    }
    if (feasiblesMap.get(g.all) == null) {
      if (TRACE) {
        System.out.println("width " + width + " infeasible");
      }
    }
  }

  public Set<XBitSet> usefulPMCs() {
    Set<XBitSet> pmcs = new HashSet<>();
    for (XBitSet cap: feasiblesMap.values()) {
      assert g.isWellSeparating(cap);
      if (g.isCliquish(cap)) {
        pmcs.add(cap);
      }
      else {
        pmcs.addAll(g.localPMCs(cap));
      }
    }
    return pmcs;
  }
  
  boolean allFeasible(ArrayList<XBitSet> components) {
    for (XBitSet compo: components) {
      if (feasiblesMap.get(compo) == null) {
        return false;
      }
    }
    return true;
  }

  Set<XBitSet> minSepsFrom(XBitSet bag) {
    Set<XBitSet> minSeps = new HashSet<>();
    LocalGraph lg = new LocalGraph(g, bag);
    MMAF mmaf = new MMAF(lg.h);
    mmaf.triangulate();
    Chordal chordal = new Chordal(lg.h);
    for (XBitSet sep: chordal.minimalSeparators()) {
      minSeps.add(sep.convert(lg.inv));
    }
    return minSeps;
  }
  
  public TreeDecomposition getTD() {
    XBitSet root = feasiblesMap.get(g.all);
    if (root == null) {
      return null;
    }
    TreeDecomposition td = new TreeDecomposition(0, 0, g);
    fillTD(root, g.all, td);
    return td;
  }
    
  XBitSet findCap(XBitSet component, XBitSet sep) {
    if (TRACE) {
      System.out.println(indent(component) + "findCap " + 
          sep + ", " + component);
    }

    XBitSet closure = component.unionWith(sep); 
    if (closure.cardinality() <= width + 1 &&
        g.isClique(component) &&
        g.fullComponents(sep).size() == 1) {
      return component.unionWith(sep);
    }
    int v0 = component.nextSetBit(0);

    ArrayList<XBitSet> candidates = sieve[v0].get(component, sep);
//    System.out.println(candidates.size() + " candidates");
    for (XBitSet cand: candidates) {
      assert feasiblesMap.get(cand) != null;
      XBitSet candSep = g.neighborSet(cand);
      assert cg.isClique(candSep);
      XBitSet union = sep.unionWith(candSep);
      if (!cg.isClique(union)) {
//        System.out.println("not clique " + union);
        continue;
      }
      assert union.cardinality() <= width + 1;

      XBitSet cap = tryUnion(component.subtract(cand).subtract(union), union);
      if (cap != null) {
        return cap;
      }
    }
//    System.out.println("v0 neighbor s in cg " + cg.neighborSet[v0] + " : " + sep);
//    System.out.println("is subset " + sep.isSubset(cg.neighborSet[v0]));
    if (sep.isSubset(cg.neighborSet[v0])) {
      return tryUnion(component.removeBit(v0), sep.addBit(v0));
    }
    return null;
  }

  XBitSet tryUnion(XBitSet scope, XBitSet union) {
    if (TRACE) {
      System.out.println(indent(scope) + "tryUnion " + 
          union + ", " + scope);
    }
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    g.listComponents(scope, union, fulls, nonFulls);
    for (XBitSet compo: nonFulls) {
//      System.out.println(feasiblesMap.get(compo) + ": " + compo);
      if (feasiblesMap.get(compo) == null) {
        if (TRACE) {
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
      if (g.isWellSeparating(union)) {
        return union;
      }
      else {
        return null;
      }
    }
    if (union.cardinality() == width + 1) {
      return null;
    }
    
    for (XBitSet full: fulls) {
      if (allOthersFeasible(fulls, full)) {
        XBitSet cap = findCap(full, union);
        if (cap != null) {
          return cap;
        }
      }
    }
    return null;
  }

  boolean allOthersFeasible(ArrayList<XBitSet> components, XBitSet component) {
    for (XBitSet compo: components) {
      if (compo == component) {
        continue;
      }
      if (feasiblesMap.get(compo) == null) {
        return false;
      }
    }
    return true;
  }
  
  
  int fillTD(XBitSet bag, XBitSet component, TreeDecomposition td) {
    if (CONSTRUCT_TD) {
      System.out.println("fillTD: bag = " + bag);
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

}

