package io.github.twalgor.improver;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Random;
import java.util.Set;

import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.MinimalizeTD;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.decomposer.SemiPID;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.sieve.SubblockSieve;

public class PIDIterative {
//  static boolean TRACE = true;
  static boolean TRACE = false;
//  static boolean TRACE_DP = true;
static boolean TRACE_DP = false;
//static boolean TRACE_PMC = true;
static boolean TRACE_PMC = false;
//static boolean TRACE_SEARCH = true;
static boolean TRACE_SEARCH = false;
static boolean VERIFY = true;
//static boolean VERIFY = false;

  static int N_CONDUCIVES = 1000;
  static boolean FINISH_BY_SEMIPID = true;
  
  Graph g;
  public int k;
  
  int budget;
  
  Map<XBitSet, Block> blockMap;
  public Map<XBitSet, PMC> pmcMap;
  
  SubblockSieve[] feasiblesSieve;
  Queue<Block> queue;
  Set<XBitSet> feasibles;
  
  Block whole;

  int nsf;
  public int nTicks;
  public boolean suspended;
  
  boolean testing;

  
  public PIDIterative(Graph g, int k) {
    super();
    this.g = g;
    this.k = k;

    if (TRACE) {
      System.out.println("PIDImprover created n " + g.n  + " m " +  g.numberOfEdges() + " k " + k);
    }

    blockMap = new HashMap<>();
    pmcMap = new HashMap<>();
    queue = new PriorityQueue<>();
    whole = makeBlock(g.all);
    
  }
  
  public PIDIterative(Graph g, int k, Set<XBitSet> pmcs) {
    this(g, k);
    importPMCs(pmcs);
  }

  public void importPMCs(Set<XBitSet> pmcs) {
    for (XBitSet pmc: pmcs) {
      makePMC(pmc);
    }
    btDP();
  }
  
  public int width() {
    return whole.width;
  }
  
  public Set<XBitSet> pmcs() {
    Set<XBitSet> pmcs = new HashSet<>();
    for (PMC p: pmcMap.values()) {
      pmcs.add(p.separator);
    }
    return pmcs;
  }
  
  void basePMCs() {
    for (int v = 0; v < g.n; v++) {
      if (g.neighborSet[v].cardinality() > k) {
        continue;
      }
      XBitSet closure = g.neighborSet[v].addBit(v);
      XBitSet rest = g.all.subtract(closure);
      XBitSet core = closure.subtract(g.neighborSet(rest));
      if (g.isClique(core) && core.nextSetBit(0) == v &&
          g.isCliquish(closure)) {
        makePMC(closure);
      }
    }  
  }
  
  void btDP() {
    for (PMC p: pmcMap.values()) {
      p.registerAsCap();
    }
    
    Block[] ba = blockMap.values().toArray(new Block[blockMap.size()]);

    Arrays.sort(ba, (b1, b2) -> XBitSet.cardinalityComparator.compare(b1.vertices, b2.vertices));

    for (Block block: ba) {
      if (block.isSmall()) {
        block.evaluate();
      }
    }
    whole.evaluate();
  }
  
  public void improve(int budget) {
    if (whole.width <= k) {
      return;
    }
    
    this.budget = budget;
    
    nTicks = 0;

    feasiblesSieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      feasiblesSieve[v] = new SubblockSieve(g, k + 1);
    }
    for (Block block: blockMap.values()) {
      block.sieved = false;
    }
    
    collectFeasibles();

    nsf = feasibles.size();
    XBitSet[] fa = feasibles.toArray(new XBitSet[feasibles.size()]);
    Arrays.sort(fa);

    queue.clear();
    for (Block block: blockMap.values()) {
      block.queued = false;
    }

    for (XBitSet feasible: fa) {
      Block block = makeBlock(feasible);
      block.enter();
    }
    
    loop();

  }
  
  public void resume(int budget) {
    this.budget = budget;
    suspended = false;
    loop();
  }
  

  void loop() {
    while (!queue.isEmpty()) {
      Block block = queue.remove();
      if (block.equals(whole)) {
        break;
      }
      if (TRACE_SEARCH) {
        System.out.println("search from " + block);
        System.out.println(queue.size() + " in queue, " + feasibles.size() + " feasibles " + blockMap.size() + " blocks " + pmcMap.size() + " pmcs");
      }
      block.search();
      if (feasibles.contains(g.all)) {
        break;
      }
      if (queue.isEmpty()) {
        collectFeasibles();
        int nsf1 = feasibles.size();
        if (nsf1 == nsf) {
//          if (VERIFY) {
//            verify();
//          }
          break;
        }
        else {
          nsf = nsf1;
          XBitSet[] fa = feasibles.toArray(new XBitSet[feasibles.size()]);
          Arrays.sort(fa);

          for (Block b: blockMap.values()) {
            b.queued = false;
          }
          for (XBitSet feasible: fa) {
            Block b = makeBlock(feasible);
            b.enter();
          }
        }
      }
      if (nTicks > budget) {
        suspended = true;
        return;
      }
    }
    btDP();
    if (TRACE) {
      System.out.println("width " + whole.width + " " + nTicks + " ticks");
    }
    
  }

  void collectFeasibles() {
    feasibles = new HashSet<>();
    for (Block block: blockMap.values()) {
      if (block.width > 0 && block.width <= k) {
        feasibles.add(block.vertices);
      }
    }
  }

  public void finish() {
    if (FINISH_BY_SEMIPID) {
      finishBySemiPID();
      return;
    }
    
    basePMCs();
    btDP();
    collectFeasibles();
    XBitSet[] fa = feasibles.toArray(new XBitSet[feasibles.size()]);
    Arrays.sort(fa);
    
    queue = new PriorityQueue<>((b1, b2) -> 
        XBitSet.cardinalityComparator.compare(b1.vertices, b2.vertices));
    
    for (Block block: blockMap.values()) {
      block.queued = false;
    }
    
    for (XBitSet feasible: fa) {
      Block block = makeBlock(feasible);
      block.enter();
    }
    
    while (!queue.isEmpty()) {
      Block block = queue.remove();
      if (block.equals(whole)) {
        return;
      }
      if (TRACE_SEARCH) {
        System.out.println("search from " + block);
        System.out.println(queue.size() + " in queue, " + feasibles.size() + " feasibles " + blockMap.size() + " blocks " + pmcMap.size() + " pmcs");
      }
      block.search();
    }
    if (VERIFY) {
      long t0 = System.currentTimeMillis();
      verify();
      System.out.println("verify took " + (System.currentTimeMillis() - t0) + " millisecs");
    }
  }
  
  void finishBySemiPID() {
    SemiPID spid = new SemiPID(g, k, false);
    if (spid.isFeasible()) {
      Set<XBitSet> pmcs = spid.conducives(N_CONDUCIVES);
      blockMap = new HashMap<>();
      pmcMap = new HashMap<>();
      queue = new PriorityQueue<>();
      whole = makeBlock(g.all);
      importPMCs(pmcs);
      btDP();
      assert whole.width <= k;
    }
    else {
      assert whole.width > k;
    }
  }

  void verify() {
    SemiPID spid = new SemiPID(g, k, false);
    boolean f = spid.isFeasible();
    if (f) {
      TreeDecomposition td = spid.getTD();
      System.out.println("k " + k + " width " + td.width + " feasible " + f + " whole.width " + whole.width);
      System.out.println("feasibles.contains(g.all) " + feasibles.contains(g.all));
      td.validate();
      td = MinimalizeTD.minimalize(td);
      Map<XBitSet, XBitSet> sFeasiblesMap = new HashMap<>();
      for (XBitSet bag: td.setOfBags()) {
        PMC p = new PMC(bag);
        XBitSet feasible = p.toCap.vertices;
        sFeasiblesMap.put(feasible, bag);
        System.out.println("feasible " + feasible + " nb " + 
            g.neighborSet(feasible) + " cap " + bag);
      }

      XBitSet[] sfa = sFeasiblesMap.keySet().toArray(new XBitSet[sFeasiblesMap.size()]);
      Arrays.sort(sfa, (s1, s2) -> XBitSet.cardinalityComparator.compare(s1, s2));
      for (XBitSet feasible: sfa) {
        XBitSet sep = g.neighborSet(feasible);
        if (!isSmall(feasible, sep, g) && !feasible.equals(g.all)) {
          continue;
        }
        if (!feasibles.contains(feasible)) {
          System.out.println("feasible missing " + feasible + " sep " + sep);
          XBitSet pmc = sFeasiblesMap.get(feasible);
          PMC p = pmcMap.get(pmc);
          if (p == null) {
            System.out.println("pmc " + pmc + " not present");
            p = makePMC(pmc);
          }
          else {
            System.out.println("pmc " + pmc + " present");
          }
          System.out.println("toCap " + p.toCap);
          System.out.println("iBlocks:");
          for (Block block: p.iBlocks) { 
            System.out.println("  " + block);
            System.out.println("  " + feasibles.contains(block.vertices) + " " + sFeasiblesMap.get(block.vertices));
          }
          ArrayList<XBitSet> components = g.separatedComponents(pmc);
          System.out.println("components:");
          for (XBitSet compo: components) {
            System.out.println("  " + compo + " " + 
                g.neighborSet(compo) + " " + pmc.subtract(g.neighborSet(compo)));
          }
        }
      }
      throw new RuntimeException("wrong infeasibility " + k);
    }
  }

  private boolean isSmall(XBitSet compo, XBitSet sep, Graph g) {
    return compo.cardinality() * 2 + sep.cardinality() <= g.n;
  }

  public TreeDecomposition getTD() {
    TreeDecomposition td = new TreeDecomposition(0, 0, g);
    whole.fillTD(td);
    return td;
  }
      
     
  public Set<XBitSet> usefulPMCs() {
    Set<XBitSet> result = new HashSet<> ();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.width() <= k) {
        result.add(pmc.separator);
      }
    }
    return result;
  }
  
  public Set<XBitSet> conducives(int nConducives) {
    Set<XBitSet> result = new HashSet<> ();
    for (PMC pmc: pmcMap.values()) {
      if (result.contains(pmc.separator)) {
        continue;
      }
      if (pmc.toCap.equals(whole) &&
          pmc.width() == whole.width) {
        pmc.collectConducives(result);
      }
      if (result.size() > nConducives) {
        return result;
      }
    }
    return result;
  }

  boolean isSmall2(XBitSet compo, XBitSet sep) {
    return compo.cardinality() * 2 + sep.cardinality() <= g.n;
  }

  PMC makePMC(XBitSet separator) {
    PMC p = pmcMap.get(separator);
    if (p == null) {
      p = new PMC(separator);
      pmcMap.put(separator, p);
    }
    return p;
  }
  
  Block makeBlock(XBitSet component)  {
    Block f = blockMap.get(component);
    if (f == null) {
      f = new Block(component);
      blockMap.put(component, f);
    }
    return f;
  }
  
  class Block implements Comparable<Block> {
    
    XBitSet vertices;
    XBitSet separator;
    int width;
    Set<PMC> caps;
    boolean queued;
    boolean sieved;
    int trial;
    
    Block(XBitSet vertices) {
      this(vertices, g.neighborSet(vertices));
    }

    Block(XBitSet vertices, XBitSet separator) {
      this.vertices = vertices;
      this.separator = separator;
      width = vertices.cardinality() + separator.cardinality() - 1;
    }
   
    void evaluate() {
      if (TRACE_DP) {
        System.out.println("evaluating " + this);
      }
      if (caps != null) {
        for (PMC cap: caps) {
           assert cap.toCap.equals(this);
           cap.evaluate();
        }
      }
      if (TRACE_DP) {
        System.out.println("evaluated " + this);
      }

    }

    void enter() {
      if (!sieved) {
        sieved = true;
        int v0 = vertices.nextSetBit(0);
        feasibles.add(vertices);
        feasiblesSieve[v0].add(vertices, separator);
      }
      if (!queued) {
        queued = true;
        queue.add(this);
      }
    }
    
    void search() {
      assert isSmall();
      
//      testing = g.n == 46 &&
//          (vertices.equals(new XBitSet(new int[] {1, 10, 11, 23, 40}))
//           || vertices.equals(new XBitSet(new int[] {30})));
      trial++;
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      XBitSet largeFull = null;
      for (XBitSet full: fulls) {
        if (!isSmall2(full, g.neighborSet(full))) {
          assert !full.equals(vertices);
          largeFull = full;
        }
      }
      if (largeFull != null) {
        search(largeFull, separator, 0);
      }
      else {
        for (XBitSet full: fulls) {
          if (full.equals(vertices)) {
            continue;
          }
          search(full, separator, 0);
        }
      }
    }

    void search(XBitSet scope, XBitSet sep, int vMin) {
      if (TRACE_SEARCH || testing) {
        System.out.println("search " + vMin + " sep " + sep + " scope " + scope + " vertices " + vertices);
        ArrayList<XBitSet> compos = g.separatedComponents(sep);
        for (XBitSet c: compos) {
          System.out.println("  " + c);
        }
      }
      nTicks++;
      //      if (nTicks > budget) {
      //        return;
      //      }
      assert sep.cardinality() <= k + 1;

      if (sep.cardinality() <= k + 1) {
        for (int w: sep.toArray()) {
          XBitSet nb = scope.intersectWith(g.neighborSet[w]);
          XBitSet union = sep.unionWith(nb);
          if (testing) {
            System.out.println(nb + " added " + union);
          }

          if (g.isPMC(union)) {
            PMC p = makePMC(union);
            p.evaluate();
            if (p.toCap.width <= k) {
              p.toCap.enter();
            }
            if (testing) {
              System.out.println("pmc " + p);
              System.out.println("  toCap " + p.toCap);
              for (Block block: p.iBlocks) { 
                System.out.println("  " + block);
              }
            }
          }
        }
      }
      
      for (int v0 = scope.nextSetBit(vMin); v0 >= 0; v0 = scope.nextSetBit(v0 + 1)) {
        ArrayList<XBitSet> candidates = feasiblesSieve[v0].get(scope, sep);
        if (TRACE_SEARCH) {
          System.out.println(candidates.size() + " candidates");
        }
        if (testing && (v0 == 1 || v0 == 30)) {
          System.out.println(candidates.size() + " candidates for v0 " + v0);
          for (XBitSet cand: candidates) {
            System.out.println("  " + cand + " this.vert " + vertices);
          }
        }
        for (XBitSet cand: candidates) {
          assert cand.isSubset(scope);
          XBitSet candSep = g.neighborSet(cand);
          XBitSet rest = scope.subtract(cand).subtract(candSep);
          XBitSet unionSep = sep.unionWith(candSep);
          assert unionSep.cardinality() <= k + 1;
          tryUnion(rest, unionSep, v0);
        }
      }


    }

    void tryUnion(XBitSet rest, XBitSet unionSep, int vMin) {
      if (TRACE_SEARCH) {
        System.out.println("tryUnion " + vMin + " unionSep " + unionSep + " rest " + rest);
      }
      ArrayList<XBitSet> components = g.componentsOf(rest);
      ArrayList<XBitSet> fulls = new ArrayList<>();
      XBitSet largeFull = null;
      for (XBitSet compo: components) {
        if (g.neighborSet(compo).equals(unionSep)) {
          fulls.add(compo);
          if (!isSmall2(compo, g.neighborSet(compo))) {
            largeFull = compo;
          }
        }
      }

      if (fulls.isEmpty()) {
        if (g.isPMC(unionSep)) {
          PMC p = makePMC(unionSep);
          if (TRACE_PMC) {
            System.out.println("pmc created " + p);
          }
          for (Block block: p.iBlocks) {
            if (!feasibles.contains(block.vertices)) {
              LocalGraph local = block.localGraph();
              TreeDecomposition td = greedyDecomposition(local.h);
              if (td.width <= k) {
                ArrayList<Block> blockList = new ArrayList<>();
                for (XBitSet bag: td.setOfBags()) {
                  XBitSet pmc = bag.convert(local.inv);
                  assert g.isPMC(pmc);
                  PMC p1 = makePMC(pmc);
                  blockList.add(p1.toCap);
                }
                blockList.sort((b1, b2) -> 
                XBitSet.cardinalityComparator.compare(b1.vertices, b2.vertices));
                for (Block b: blockList) {
                  b.evaluate();
                  assert b.width <= k;
                  b.enter();
                }
              }
            }
          }
          p.evaluate();
          if (p.toCap.width <= k) {
            p.toCap.enter();
          }
        }        
        return;
      }
      if (unionSep.cardinality() == k + 1) {
        return;
      }

      for (XBitSet full: fulls) {
        if (largeFull == null || full == largeFull)
          search(full, unionSep, vMin + 1);
      }
    }

    XBitSet largestOf(XBitSet[] vSets) {
      XBitSet largest = null;
      for (XBitSet vs: vSets) {
        if (largest == null ||
            XBitSet.cardinalityComparator.compare(vs, largest) > 0) {
          largest = vs;
        }
      }
      return largest;
    }

    LocalGraph localGraph() {
      return new LocalGraph(g, vertices.unionWith(separator));
    }

    void addCap(PMC cap) {
      if (TRACE_PMC) {
        System.out.println("adding cap " + cap.separator + " to " + this);
      }
      if (caps == null) {
        caps = new HashSet<>();
      }
      caps.add(cap);
    }
      
    int fillTD(TreeDecomposition td) {
      PMC cap = bestCap();
      if (cap == null) {
        if (TRACE) {
          System.out.println("cap is null " + this);
        }
        LocalGraph local = localGraph();
        TreeDecomposition td1 = greedyDecomposition(local.h);
        int r = findBagContaining(td1, separator.convert(local.conv));
        return fillTDFromTD(td1, r, 0, local.inv, td);
      }
      assert cap.width() <= whole.width: cap.width() + " : " + whole.width;
      int b = td.addBag(cap.separator.toArray());
      for (Block f: cap.iBlocks) {
        if (f.vertices.isSubset(vertices)) {
          int b1 = f.fillTD(td);
          td.addEdge(b,  b1);
        }
      }
      return b;
    }

    int fillTDFromTD(TreeDecomposition fromTD, int fromB, int p, int[] conv, TreeDecomposition td) {
      int b = td.addBag(fromTD.bagAt(fromB).convert(conv).toArray());
      for (int fromB1: fromTD.neighbor[fromB]) {
        if (fromB1 == p) {
          continue;
        }
        int b1 = fillTDFromTD(fromTD, fromB1, fromB, conv, td);
        td.addEdge(b, b1);
      }
      return b;
    }

    int findBagContaining(TreeDecomposition td, XBitSet vs) {
      for (int b = 1; b <= td.nb; b++) {
        if (vs.isSubset(td.bagAt(b))) {
          return b;
        }
      }
      return -1;
    }

    PMC bestCap() {
      if (caps == null) {
        return null;
      }
      PMC best = null;
      int width = 0;
      for (PMC cap: caps) {
        int w = cap.width();
        if (best == null || w < width)  {
          best = cap;
          width = w;
        }
      }
      return best;
    }

    @Override 
    public int hashCode() {
      return vertices.hashCode();
    }
    
    @Override 
    public boolean equals(Object x) {
      Block f = (Block) x;
      return vertices.equals(f.vertices);
    }

    @Override
    public int compareTo(Block f) {
      if (trial != f.trial) { 
        return trial - f.trial;
      }
      return - XBitSet.cardinalityComparator.compare(vertices, f.vertices);
    }
    
    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("Block: separator " + separator + " vertices " + vertices + 
          " width " + width + " sieved " + sieved + " queued " + queued);
      if (caps != null) {
        sb.append(" caps " + caps.size());
      }
      return sb.toString();
    }

    Block theOtherBlock(XBitSet sep) {
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      assert fulls.size() >= 2;
      for (XBitSet full: fulls) {
        if (full.intersects(sep)) {
          return makeBlock(full);
        }
      }
      assert false;
      return null;
    }

    boolean isSmall() {
      return isSmall2(vertices, separator);
    }
  }
  
  class PMC {
    XBitSet separator;
    Block[] iBlocks;
    Block toCap;
    
    PMC(XBitSet separator) {
      if (TRACE_PMC) {
        System.out.println("PMC being created " + separator);
      }
      assert g.isPMC(separator);
      this.separator = separator;
      ArrayList<XBitSet> components = g.separatedComponents(separator);
      components.sort((c1, c2) -> - XBitSet.cardinalityComparator.compare(c1, c2));
      iBlocks = new Block[components.size()];
      for (int i = 0; i < iBlocks.length; i++) {
        iBlocks[i] = makeBlock(components.get(i));
      }
      
      XBitSet inner = smallInner();
      if (inner == null) {
        toCap = makeBlock(g.all);
      }
      else {
        toCap = makeBlock(inner);
        ArrayList<Block> iBlockList = new ArrayList<>();
        for (Block block: iBlocks) {
          if (block.vertices.isSubset(inner)) {
            iBlockList.add(block);
          }
        }
        iBlocks = iBlockList.toArray(new Block[iBlockList.size()]);
      }
      
      if (TRACE_PMC) {
        System.out.println("  toCap " + toCap);
      }

      toCap.addCap(this);
    }

    XBitSet smallInner() {
      Set<XBitSet> seps = new HashSet<>();
      for (Block iBlock: iBlocks) {
        seps.add(iBlock.separator);
      }
      XBitSet[] sa = seps.toArray(new XBitSet[seps.size()]);
      Arrays.sort(sa, (s1, s2) -> - XBitSet.cardinalityComparator.compare(s1, s2));
      for (XBitSet sep: sa) {
        XBitSet inner = innerOf(sep);
        if (inner != null) {
          return inner;
        }
      }
      return null;
    }
    
    XBitSet innerOf(XBitSet sep) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      XBitSet largest = null;
      XBitSet inner = null;
      for (XBitSet full: fulls) {
        if (full.intersects(separator)) {
          inner = full;
        }
        if (largest == null || XBitSet.cardinalityComparator.compare(full, largest) > 0) {
          largest = full;
        }
      }
      if (isSmall2(inner, sep) && inner != largest) {
        return inner;
      }
      else {
        return null;
      }
    }

    void evaluate() {
      int w = width();
      if (w < toCap.width) {
        toCap.width = w;
      }
    }
    
    int width() {
      int width = separator.cardinality() - 1;
      for (Block block: iBlocks) {

        if (block.width > width) {
          width = block.width;
        }
      }
      if (width < toCap.width) {
        toCap.width = width;
      }
      return width;
    }

    void collectConducives(Set<XBitSet> result) {
      if (result.contains(separator)) {
        return;
      }
      result.add(separator);
      for (Block f: iBlocks) {
        PMC cap = f.bestCap();
        if (cap != null) {
          f.bestCap().collectConducives(result);
        }
        else {
          LocalGraph local = f.localGraph();
          TreeDecomposition td = greedyDecomposition(local.h);
          result.addAll(XBitSet.convertAll(td.setOfBags(), local.inv));
        }
      }
    }

    int widthFor(XBitSet component) {
//      System.out.println("value for " + component + " " + this);
      int w = separator.cardinality() - 1;
//      System.out.println("initial value " + val);
      for (Block f: iBlocks) {
        if (f.vertices.isSubset(component)) {
//          System.out.println(" block " + f);
          if (f.width == 0) {
            return 0;
          }
          if (f.width > w) {
            w = f.width;
          }
        }
      }
      return w;
    }
    
    void registerAsCap() {
      toCap.addCap(this);
    }
    
    @Override
    public String toString() {
      return "pmc " + separator + " " + iBlocks.length + " blocks";
    }
  }
  
  static TreeDecomposition greedyDecomposition(Graph h) {
    Graph t = h.copy();
    MMAF mmaf = new MMAF(t);
    mmaf.triangulate();
    TreeDecomposition td = Chordal.chordalToTD(t);
    td.g = h;
    return td; 
  }

    
  static void test1(String group, String name) {
    File file = new File(group + "/" + name + ".gr");
    Graph g0 = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g0.n + ",  m =" + g0.numberOfEdges());
    System.out.println("isConnected " + g0.isConnected(g0.all));
    ArrayList<XBitSet> components = g0.componentsOf(g0.all);
    
    XBitSet compo = XBitSet.largest(components);
    
    System.out.println("largest " + compo);
    
    Subgraph sub = new Subgraph(g0, compo);
    
    Graph g = sub.h;
    long t0 = System.currentTimeMillis();
//    TreeDecomposition td = greedyDecomposition(g);
    
//    Random random = new Random(1);
//    for (int b = 1; b <= td.nb; b++) {
//      td.bags[b] = Arrays.copyOf(td.bags[b], td.bags[b].length + 3);
//      td.bags[b][td.bags[b].length - 1] = random.nextInt(3);
//      td.bags[b][td.bags[b].length - 2] = 3 + random.nextInt(3);
//      td.bags[b][td.bags[b].length - 3] = 6 + random.nextInt(3);
//    }
//    td.width += 3;
    TreeDecomposition td = terribleDecomposition(g);
    td = MinimalizeTD.minimalize(td);
    System.out.println("greedy width " + td.width + " " + 
        (System.currentTimeMillis() - t0) + " millisecs");

    PIDIterative pidIter = new PIDIterative(g, td.width - 1);

    pidIter.importPMCs(td.setOfBags());
    System.out.println("initial width " + pidIter.whole.width + " " + 
        (System.currentTimeMillis() - t0) + " millisecs");

    pidIter.improve(100000);
    System.out.println("current width " + pidIter.whole.width);
    pidIter.improve(130000);
    System.out.println("current width " + pidIter.whole.width);
    pidIter.improve(100000);
    System.out.println("current width " + pidIter.whole.width);
    pidIter.improve(100000);
    System.out.println("current width " + pidIter.whole.width);
    pidIter.improve(100000);
    System.out.println("current width " + pidIter.whole.width);
    pidIter.finish();
 
    td = pidIter.getTD();
    System.out.println("final width " + td.width + " " + pidIter.nTicks + " ticks " +  
      (System.currentTimeMillis() - t0) + " millisecs");
    td.validate();
    
  }


  static TreeDecomposition terribleDecomposition(Graph g) {
    Graph h = g.copy();
    XBitSet remaining = XBitSet.all(g.n);
    for (int v = 0; v < g.n; v++) {
      XBitSet nb = h.neighborSet[v].intersectWith(remaining);
      h.fill(nb);
      remaining.clear(v);
    }
    TreeDecomposition td = Chordal.chordalToTD(h);
    td.g = g;
    return td;
  }

  public static void main(String[] args) {
//    test("..\\instance\\PACE2017bonus_gr", "Promedus_12_14");
//    test("pace17exact", "ex001", 10000);
//    test("pace17exact", "ex003", 1000);
//    test("pace17exact", "ex005", 1000);
//    test("pace17exact", "ex007", 1000);
//    test("pace17exact", "ex009", 1000);
//    test("pace17exact", "ex011", 1000);
//    test("pace17exact", "ex013", 1000);
//    test("pace17exact", "ex015", 1000);
//    test("pace17exact", "ex017", 1000);
//    test("pace17exact", "ex019", 1000);
//    test("pace17exact", "ex021", 1000);
//    test("pace17exact", "ex103", 1000);
//    test("pace17exact", "ex117", 1000);
//    test("pace17exact", "ex118", 1000);
//    test("pace17exact", "ex167", 1000);
//    test("grid", "troidal4_4", 1000);
//    test("grid", "troidal5_5", 100);
//    test("grid", "troidal6_6", 1000);
//    test("grid", "troidal7_7", 1000);
//    test("grid", "troidal8_8", 1000);
//    test("coloring", "fpsol2.i.1", 1000); // 66
//    test("coloring", "fpsol2.i.2", 1000); // 31
//    test("coloring", "fpsol2.i.3", 1000000); // 31
//    test("coloring", "mulsol.i.1", 1000000); // 50
//    test("coloring", "mulsol.i.2", 1000000); // 32
//    test("coloring", "mulsol.i.3", 1000000); // 32
//    test("coloring", "inithx.i.1", 1000000); // 56
//    test("coloring", "inithx.i.2", 1000000); // 31
//  test("coloring", "inithx.i.3", 1000000); // 31
//    test("coloring", "queen9_9", 1000);
//    test("coloring", "queen8_8", 1000);
//    test("coloring", "queen6_6", 1000);
//    test("coloring", "queen5_5", 1000);
//    test1(".", "obs_Promedus_38_15");
    test1(".", "obs_ex086");
    
  }

}
