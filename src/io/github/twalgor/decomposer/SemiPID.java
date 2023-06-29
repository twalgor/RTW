package io.github.twalgor.decomposer;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.MinimalizeTD;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.minseps.MinSepsGenerator;
import io.github.twalgor.sieve.SubblockSieve;

public class SemiPID {
  static final int LINE_LENGTH =50;
//  static final boolean VALIDATE = true;
  static final boolean VALIDATE = false;
//  static final boolean CONSTRUCT_TD = true;
static final boolean CONSTRUCT_TD = false;
//  static final boolean VERBOSE = true;
//  static final boolean VERBOSE = false;
//  static final boolean TRACE = true;
  static boolean TRACE = false;
//  static final boolean TRACE_ROOT = true;
  static final boolean TRACE_ROOT = false;
  
  Graph g;
  String graphName;
  public int k;
  public Set<XBitSet> minSeps;
  boolean pmcOnly;
  public Map<XBitSet, XBitSet> feasiblesMap;
  ArrayList<XBitSet> minSeparateds;
  
  XBitSet rootKnown;
  ArrayList<XBitSet> composOfRoot;
  XBitSet firstCompoOfRoot;
  
  SubblockSieve[] sieve;
  SubblockSieve[] sieveForRoot;
  
  XBitSet root;
  String rootType;
  int[] convForRoot;
  int[] invForRoot;

  public static TreeDecomposition decompose(Graph g) {
    return decompose(g, false);
  }

  public static TreeDecomposition decompose(Graph g, boolean pmcOnly) {
    for (int k = g.minDegree(); k < g.n; k++) {
      SemiPID spid = new SemiPID(g, k, pmcOnly);
      TreeDecomposition td = spid.decompose();
      if (td != null) {
        return td;
      }
    }
    assert false: g.n + ", " + g.numberOfEdges();
    return null;
  }

  public SemiPID(Graph g, int k, boolean pmcOnly) {
    this.g = g;
    this.k = k;
    this.pmcOnly = pmcOnly;
    MinSepsGenerator msg = new MinSepsGenerator(g, k);
    msg.generate();
    minSeps = msg.minSeps;
  }
   
  public SemiPID(Graph g, int k, Set<XBitSet> minSeps, boolean pmcOnly) {
    this.g = g;
    this.k = k;
    this.minSeps = minSeps;
    this.pmcOnly = pmcOnly;
  }
  
  public Set<XBitSet> getCaps() {
    Set<XBitSet> caps = new HashSet<>();
    for (XBitSet msc: minSeparateds) {
      XBitSet cap = feasiblesMap.get(msc);
      if (cap != null) {
        caps.add(cap);
      }
    }
    return caps;
  }
  
  public Set<XBitSet> usefulMinSeps() {
    Set<XBitSet> seps = new HashSet<>();
    for (XBitSet msc: minSeparateds) {
      XBitSet cap = feasiblesMap.get(msc);
      if (cap != null) {
        seps.add(g.neighborSet(msc));
      }
    }
    return seps;
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
    TreeDecomposition td = getTD();
    td = MinimalizeTD.minimalize(td);
    pmcs.addAll(td.setOfBags());
    return pmcs;
  }

  public TreeDecomposition decompose() {
    if (k >= g.n - 1) {
      TreeDecomposition td = new TreeDecomposition(0, g.n - 1, g);
      td.addBag(g.all.toArray());
      td.degree[1] = 0;
      td.neighbor[1] = new int[0];
      return td;
    }
    if (!g.isConnected(g.all)) {
      ArrayList<XBitSet> components = g.componentsOf(g.all);
      if (TRACE) {
        System.out.println(components.size() + " connected components");
      }
      TreeDecomposition td = new TreeDecomposition(0, 0, g);
      for (XBitSet compo: components) {
        Subgraph sub = new Subgraph(g, compo);
        SemiPID spid = new SemiPID(sub.h, k, null, pmcOnly);
        TreeDecomposition td1 = spid.decompose();
        if (td1 == null) {
          return null;
        }
        int base = td.nb;
        for (int b1 = 1; b1 <= td1.nb; b1++) {
          int b = td.addBag(
              new XBitSet(td1.bags[b1]).convert(sub.inv).toArray());
          td.degree[b] = td1.degree[b1];
          assert td1.neighbor[b1] != null;
          assert td.neighbor != null;
          td.neighbor[b] = new int[td1.neighbor[b1].length];
          for (int i = 0; i < td1.neighbor[b1].length; i++) {
            td.neighbor[b][i] = td1.neighbor[b1][i] + base;
          }
        }
        if (base != 0) {
          td.addEdge(1, base + 1);
        }
        if (td1.width > td.width) {
          td.width = td1.width;
        }
      }
      return td;
    }
    if (minSeps == null) {
      MinSepsGenerator msg = new MinSepsGenerator(g, k);
      msg.generate();
      minSeps = msg.minSeps;
    }
    
    dp();

    root = findRoot();
    if (root == null) {
      return null;
    }
//    System.out.println("root = " + root);
//    ArrayList<XBitSet> components = g.separatedComponents(root);
//    for (XBitSet compo: components) {
//      System.out.println(compo);
//      System.out.println("...cap is " + feasiblesMap.get(compo));
//      System.out.println("...sep is " + g.neighborSet(compo));
//    }
    TreeDecomposition td = new TreeDecomposition(0, k, g);
    fillTD(root, g.all, td);
    return td;
  }
  
  public boolean isFeasible() {
    if (k >= g.n - 1) {
      return true;
    }
    if (!g.isConnected(g.all)) {
      ArrayList<XBitSet> components = g.componentsOf(g.all);
      for (XBitSet compo: components) {
        Subgraph sub = new Subgraph(g, compo);
        SemiPID spid = new SemiPID(sub.h, k, null, pmcOnly);
        if (!spid.isFeasible()) {
          return false;
        }
      }
      return true;
    }
    
    if (minSeps == null) {
      MinSepsGenerator msg = new MinSepsGenerator(g, k);
      msg.generate();
      minSeps = msg.minSeps;
    }
    
    dp();
    root = findRoot();
    return root != null;
  }
  
  public TreeDecomposition getTD() {
    TreeDecomposition td = new TreeDecomposition(0, k, g);
    fillTD(root, g.all, td);
    return td;
  }

  public void dp() {
    minSeparateds = new ArrayList<>();
    
    for (XBitSet sep: minSeps) {
      assert sep.cardinality() <= k;
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      for (XBitSet full: fulls) {
        if (isSmall(full)) {
          minSeparateds.add(full);
        }
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
  
  public Set<XBitSet> conducives(int nConducives) {
    Set<XBitSet> conducives = new HashSet<>();
    XBitSet[] fa = feasiblesMap.keySet().toArray(
        new XBitSet[feasiblesMap.size()]);
    Arrays.sort(fa, (f1, f2) -> -XBitSet.cardinalityComparator.compare(f1,  f2));
    for (XBitSet f: fa) {
      XBitSet cap = feasiblesMap.get(f);
      conducivesFrom(cap, conducives);
      if (conducives.size() >= nConducives) {
        break;
      }
    }
    
    return conducives;
  }
  
  void conducivesFrom(XBitSet cap, Set<XBitSet> conducives) {
//    System.out.println("conducives from " + cap);
    ArrayList<XBitSet> components = g.componentsOf(cap);
    for (XBitSet compo: components) {
      if (feasiblesMap.get(compo) == null) {
//        System.out.println("looking for cap of comop " + compo);
        XBitSet cap1 = findCap(compo, g.neighborSet(compo), null);
        if (cap1 == null) {
          return;
        }
//        System.out.println("cap " + cap1 + " found for " + compo);
        feasiblesMap.put(compo, cap1);  
      }
    }
//    System.out.println("now generate from " + cap);
    findConducives(cap, g.all, conducives);
  }
  
  public Set<XBitSet> conducivesOld() {
    XBitSet root = findRoot();
    if (root == null) {
      return null;
    }
    Set<XBitSet> conducives = new HashSet<>();
    if (g.isWellFormedBag(root)) {
      conducives.addAll(pmcsFrom(root, g));
    }
    findConducives(root, g.all, conducives);
    return conducives;
  }
  
  void findConducives(XBitSet bag, XBitSet component, Set<XBitSet> conducives) {
    ArrayList<XBitSet> components = g.componentsOf(component.subtract(bag));
    for (XBitSet compo: components) {
      XBitSet cap = feasiblesMap.get(compo);
      if (cap == null) {
        return;
      }
      conducives.addAll(pmcsFrom(cap, g));
      assert cap != null;
      findConducives(cap, compo, conducives);
    }
  }
  
  Set<XBitSet> pmcsFrom(XBitSet bag, Graph h) {
    assert h.isWellFormedBag(bag);
    
    Set<XBitSet> pmcs = new HashSet<>();
    LocalGraph lg = new LocalGraph(h, bag);
    if (lg.h.isClique(lg.h.all)) {
      assert h.isPMC(bag);
      pmcs.add(bag);
      return pmcs;
    }
    TreeDecomposition td = SemiPID.decompose(lg.h);
    td = minimalize(td);
    for (XBitSet bag1: td.setOfBags()) {
//      assert h.isPMC(bag1);
      if(h.isPMC(bag1)) {
        pmcs.add(bag1);
      }
    }
    return pmcs;
  }

  TreeDecomposition minimalize(TreeDecomposition td) {
    MinimalizeTD mtd = new MinimalizeTD(td.g, td);
    return mtd.minimalize();
  }


  public XBitSet findRoot() {
    for (XBitSet cand: feasiblesMap.keySet()) {
      XBitSet candSep = g.neighborSet(cand);
      if (isAllFeasible(candSep)) {
        return candSep;
      }
    }
    
    int[] count = new int[g.n];
    
    for (XBitSet f: feasiblesMap.keySet()) {
      for (int v = f.nextSetBit(0); v >= 0; v = f.nextSetBit(v + 1)) {
        count[v]++;
      }
    }
    
    Integer[] ord = new Integer[g.n];
    for (int v = 0; v < g.n; v++) {
      ord[v] = v;
    }
    Arrays.sort(ord, (u, v) -> count[u] == count[v]? u - v: count[u] - count[v]);

    if (TRACE_ROOT || rootKnown != null) { 
      System.out.println(Arrays.toString(ord));
    }
    
    convForRoot = new int[g.n];
    invForRoot = new int[g.n];
    for (int i = 0; i < g.n; i++) {
      invForRoot[i] = ord[i];
      convForRoot[ord[i]] = i;
    }
    
    if (rootKnown != null) {
      composOfRoot = g.separatedComponents(rootKnown);
      firstCompoOfRoot = null;
      for (XBitSet compo: composOfRoot) {
        if (firstCompoOfRoot == null || 
            convForRoot[smallestForRoot(compo)] < 
            convForRoot[smallestForRoot(firstCompoOfRoot)]) {
          firstCompoOfRoot = compo;
        }
      }
//      System.out.println("first compo of known root = " + firstCompoOfRoot);
    }

    sieveForRoot = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      sieveForRoot[v] = new SubblockSieve(g, k + 1);
    }
    for (XBitSet feasible: feasiblesMap.keySet()) {
      int v0 = smallestForRoot(feasible);
      XBitSet sep = g.neighborSet(feasible);
      sieveForRoot[v0].add(feasible, g.neighborSet(feasible));
    }

    XBitSet forced = new XBitSet(g.n);
    for (int i = 0; i < k + 1; i++) {
      int v0 = ord[i];
      ArrayList<XBitSet> candidates = sieveForRoot[v0].get(g.all, new XBitSet());
//      System.out.println("v0 = " + v0);
//      for (XBitSet cand: candidates) {
//        System.out.println(" " + cand);
//      }
      for (XBitSet cand: candidates) {
        if (TRACE_ROOT) {
          System.out.println("trying candidate " + cand);
        }
        if (cand.equals(firstCompoOfRoot)) {
//          System.out.println("candidate " + cand + " is the first compo of known root");
        }

        XBitSet candSep = g.neighborSet(cand);
        if (forced.isSubset(candSep)) {
          ArrayList<XBitSet> fulls = new ArrayList<>();
          ArrayList<XBitSet> nonFulls = new ArrayList<>();
          g.listComponents(g.all.subtract(cand.unionWith(candSep)), candSep, fulls, nonFulls);
          assert !fulls.isEmpty();
          XBitSet largest = null;
          for (XBitSet full: fulls) {
            if (largest == null || full.cardinality() > largest.cardinality()) {
              largest = full;
            }
          }
          if (TRACE_ROOT || cand.equals(firstCompoOfRoot)) {
            System.out.println(indent(largest) + "largest the other " + largest);
          }

          boolean smallInfeasible = false;
          for (XBitSet full: fulls) {
            if (full != largest &&
                feasiblesMap.get(full) == null) {
              smallInfeasible = true;
            }
          }
          for (XBitSet compo: nonFulls) {
            if (feasiblesMap.get(compo) == null) {
              smallInfeasible = true;
            }
          }
          if (TRACE_ROOT || cand.equals(firstCompoOfRoot)) {
            System.out.println(indent(largest) + "smallInfeasible = "+ smallInfeasible);
          }

          if (smallInfeasible) {
            continue;
          }
          XBitSet cap = null;
          if (cand.equals(firstCompoOfRoot)) {
            cap = findCapForRoot(largest, candSep, rootKnown);
          }
          else {
            cap = findCapForRoot(largest, candSep, null);
          }
          if (cap != null) {
            return cap;
          }          
        }
        else {
          XBitSet union = forced.unionWith(candSep);
          if (union.cardinality() > k + 1) {
            continue;
          }
          XBitSet rest = g.all.subtract(union).subtract(cand);
          if (TRACE_ROOT || cand.equals(firstCompoOfRoot)) {
            System.out.println(indent(g.all.subtract(candSep)) + "union = " + union);
            System.out.println(indent(g.all.subtract(candSep)) + "known root = " + rootKnown);
          }
          XBitSet cap = null;
          if (rootKnown != null && union.isSubset(rootKnown)) {
            cap = tryUnionForRoot(rest, union, rootKnown);
          }
          else {
            cap = tryUnionForRoot(rest, union, null);
          }
          if (cap != null) {
            return cap;
          }
        }
      }
      forced.set(v0);
      if (i == k) {
        if (g.fullComponents(forced).isEmpty() &&
            g.isCliquish(forced) &&
            isAllFeasible(forced)) {
          return forced;
        }
      }
    }
    return null;
  }

  private int smallestForRoot(XBitSet compo) {
    return invForRoot[compo.convert(convForRoot).nextSetBit(0)];
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

  boolean isAllSmall(XBitSet pmc) {
    ArrayList<XBitSet> components = g.componentsOf(g.all.subtract(pmc));
    for (XBitSet compo: components) {
      if (!isSmall(compo)) {
        return false;
      }
    }
    return true;
  }
  boolean isSmall(XBitSet component) {
    return 2 * component.cardinality() <= 
        g.n - (g.neighborSet(component).cardinality());
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

  XBitSet findCapForRoot(XBitSet component, XBitSet sep, XBitSet capKnown) {
    boolean toTrace = false;
    if (capKnown != null && sep.isSubset(capKnown) &&
        capKnown.isSubset(component.unionWith(sep))) {
      System.out.println(indent(component) + 
          "compo:" + component + " and sep:"  + sep +
          " consistent with known cap " + capKnown);
      toTrace = true;
    }
    if (component.cardinality() + sep.cardinality() <= k + 1 &&
        g.isClique(component)) {
      return component.unionWith(sep);
    }
    int v0 = smallestForRoot(component);

    ArrayList<XBitSet> candidates = sieveForRoot[v0].get(component, sep);
    if (TRACE_ROOT || toTrace) {
      System.out.println(indent(component) + candidates.size() + " candidates");
    }

    for (XBitSet cand: candidates) {
      XBitSet candSep = g.neighborSet(cand);
      if (TRACE_ROOT || toTrace) {
        System.out.println(indent(component) + "cand = " + cand);
        System.out.println(indent(component) + "candSep = " + candSep);
      }
      XBitSet union = sep.unionWith(candSep);
      assert !union.equals(sep);
      assert union.cardinality() <= k + 1;
//      System.out.println("component = " + component);
//      System.out.println("cand = " + cand);
//      System.out.println("sep = " + sep);
//      System.out.println("union = " + union);
      XBitSet cap = tryUnionForRoot(component.subtract(cand).subtract(union), union, capKnown);
      if (cap != null) {
        return cap;
      }
    }
    if (TRACE_ROOT || toTrace) {
      System.out.println(indent(component) + v0 + " should be in tha bag");
    }
    return tryUnionForRoot(component.removeBit(v0), sep.addBit(v0), capKnown);
  }
  
  XBitSet tryUnionForRoot(XBitSet scope, XBitSet union, XBitSet capKnown) {
    boolean toTrace = false;
    if (capKnown != null && union.isSubset(capKnown) &&
        capKnown.isSubset(scope.unionWith(union))) {
      System.out.println(indent(scope) + "tryUnionForRoot" + 
          ", scope:" + scope + " and union:"  + union +
          " consistent with known cap " + capKnown);
      toTrace = true;
    }

    if (TRACE_ROOT) {
      System.out.println(indent(scope) + "tryUnionForRoot " + 
          scope + ", " + union);
    }
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    g.listComponents(scope, union, fulls, nonFulls);
    if (TRACE_ROOT) {
      System.out.println(indent(scope) + fulls.size() + " fulls and " + 
          nonFulls.size() + " non fulls");
    }
    for (XBitSet compo: nonFulls) {
      if (TRACE_ROOT) {
        System.out.println(indent(compo) + compo + ": " + feasiblesMap.get(compo));
      }
      if (feasiblesMap.get(compo) == null) {
        if (TRACE_ROOT || toTrace) {
          System.out.println(indent(scope) + "infeasible, returninig null, compo = " + compo);
        }
        return null;
      }
    }
    if (fulls.isEmpty()) {
      if (TRACE_ROOT || toTrace) {
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
    XBitSet fullToExtend = null;
    if (fulls.size() == 1) {
      fullToExtend = fulls.get(0);
    }
    else {
      for (XBitSet full: fulls) {
        if (feasiblesMap.get(full) != null) {
          continue;
        }
        if (isSmall(full)) {
          if (TRACE_ROOT || toTrace) {
            System.out.println(indent(scope) + 
                "infeasible small full that is minimally separated");
            System.out.println(" returninig null");
          }
          return null;
        }
        else {
          assert fullToExtend == null;
          fullToExtend = full;
        }
      }
      if (fullToExtend == null) {
        if (TRACE_ROOT || toTrace) {
          System.out.println(indent(scope) + 
              "at least two fulls, all feasible, returninig " + union);
        }
        return union;
      }
    }
    if (union.cardinality() == k + 1) {
      if (TRACE_ROOT || toTrace) {
        System.out.println(indent(scope) + 
            "no room for extending, returninig null");
      }
      return null;
    }
    return findCapForRoot(fullToExtend, union, capKnown);
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
  
  static void test1(String project, String group, String name, int width) {
    File file = new File("../" + project + "/instance/" + group + "/" + name + ".gr");
    Graph g = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g.n + ",  m =" + g.numberOfEdges());

    for (int k = width - 1; k <= width; k++) {
      System.out.println("trying width " + k);
      long t0 = System.currentTimeMillis();
      MinSepsGenerator msnn = new MinSepsGenerator(g, k);
      msnn.generate();
      System.out.println(msnn.minSeps.size() + " minseps in " + 
          (System.currentTimeMillis() - t0) + " millisecs");
      msnn.generate();
//      SemiPID spid = new SemiPID(g, k, msnn.minSeps, true);
      SemiPID spid = new SemiPID(g, k, msnn.minSeps, false);
      spid.dp();
      System.out.println(msnn.minSeps.size() + " dp done  in " + 
          (System.currentTimeMillis() - t0) + " millisecs");

      XBitSet root = spid.findRoot();
      if (root == null) {
        System.out.println("width " + k + " infeasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      else {
        System.out.println("width " + k + " feasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
    }
  }
  
  static void decompose(String group, String name) {
    File file = new File("instance/" + group + "/" + name + ".gr");
    Graph g = Graph.readGraph(file);
    TreeDecomposition td = decompose(g);
    td.save("td/" + group + "/" + name + ".td");
  }
  static void test(String group, String name) {
    File file = new File("../instance/" + group + "/" + name + ".gr");
    Graph g = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g.n + ",  m =" + g.numberOfEdges());

    for (int k = g.minDegree(); k <= g.n; k++) {
      System.out.println("trying width " + k);
      long t0 = System.currentTimeMillis();
      MinSepsGenerator msnn = new MinSepsGenerator(g, k);
      msnn.generate();
      System.out.println(msnn.minSeps.size() + " minseps in " + 
          (System.currentTimeMillis() - t0) + " millisecs");
      msnn.generate();
//      SemiPID spid = new SemiPID(g, k, msnn.minSeps, true);
      SemiPID spid = new SemiPID(g, k, msnn.minSeps, false);
      TreeDecomposition td = spid.decompose();
      System.out.println(msnn.minSeps.size() + " dp done  in " + 
          (System.currentTimeMillis() - t0) + " millisecs");

      if (td == null) {
        System.out.println("width " + k + " infeasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      else {
        System.out.println("width " + k + " feasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
        td.validate();
        break;
      }
    }
  }
  
  static void test2(String path) {
    File file = new File(path);
    Graph g = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g.n + ",  m =" + g.numberOfEdges());

    System.out.println("isConnected " + g.isConnected(g.all));
    Graph h = g.copy();
    MMAF mmaf = new MMAF(h);
    mmaf.triangulate();
    System.out.println("mmaf width " + mmaf.width);
    
    for (int k = g.minDegree(); k <= g.n; k++) {
      System.out.println("trying width " + k);
      long t0 = System.currentTimeMillis();
      MinSepsGenerator msnn = new MinSepsGenerator(g, k);
      msnn.generate();
      System.out.println(msnn.minSeps.size() + " minseps in " + 
          (System.currentTimeMillis() - t0) + " millisecs");
      msnn.generate();
//      SemiPID spid = new SemiPID(g, k, msnn.minSeps, true);
      SemiPID spid = new SemiPID(g, k, msnn.minSeps, false);
      TreeDecomposition td = spid.decompose();
      System.out.println(msnn.minSeps.size() + " dp done  in " + 
          (System.currentTimeMillis() - t0) + " millisecs");

      if (td == null) {
        System.out.println("width " + k + " infeasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      else {
        System.out.println("width " + k + " feasible, " + 
            (System.currentTimeMillis() - t0) + " millisecs");
        td.validate();
        break;
      }
    }
    
    for (int k = g.minDegree(); k <= g.n; k++) {
      System.out.println("trying width " + k + " for SemiPIDFull");
      long t0 = System.currentTimeMillis();
      SemiPIDFull spidfull = new SemiPIDFull(g, k);
      spidfull.computeSafeSeps();
      System.out.println(spidfull.safeSeps.size() + " safeSeps");
      if (!spidfull.safeSeps.isEmpty()) {
        break;
      }
    }

  }
  public static void main(String[] args) {
//    test2("SemiPIDBug.gr");
//    test("grid", "troidal4_4");
//    test("grid", "troidal5_5");
//    test("grid", "troidal6_6");
    test("grid", "troidal7_7");
  }
}

