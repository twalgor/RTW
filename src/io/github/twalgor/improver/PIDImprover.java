package io.github.twalgor.improver;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import io.github.twalgor.btdp.Value;
import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.sieve.SubblockSieve;

public class PIDImprover {
//  static boolean TRACE = true;
  static boolean TRACE = false;
//  static boolean TRACE_DP = true;
  static boolean TRACE_DP = false;
  static int N_CONDUCIVES = 1000;
  
  Graph g;
  public int k;
  
  int budget;
  
  Map<XBitSet, Block> blockMap;
  public Map<XBitSet, PMC> pmcMap;
  Set<Block> newBlocks;
  
  SubblockSieve[] subfeasiblesSieve;
  Queue<Block> queue;
  Set<Block> processed;
  
  public Value opt;
  
  Block whole;
  
  int nTicks;
  
  public PIDImprover(Graph g) {
    super();
    this.g = g;

    if (TRACE) {
      System.out.println("ResourceBoundedPID created n " + g.n  + " m " +  g.numberOfEdges());
    }

    blockMap = new HashMap<>();
    pmcMap = new HashMap<>();
    queue = new PriorityQueue<>();
    whole = makeBlock(g.all);
  }
  
  public PIDImprover(Graph g, Set<XBitSet> pmcs) {
    this(g);
    importPMCs(pmcs);
  }

  public void importPMCs(Set<XBitSet> pmcs) {
    for (XBitSet pmc: pmcs) {
      makePMC(pmc);
    }
    doDP();
  }
  
  public Set<XBitSet> pmcs() {
    Set<XBitSet> pmcs = new HashSet<>();
    for (PMC p: pmcMap.values()) {
      pmcs.add(p.separator);
    }
    return pmcs;
  }
  
  void doDP() {
    for (PMC p: pmcMap.values()) {
      p.registerAsCap();
    }
    
    Block[] ba = blockMap.values().toArray(new Block[blockMap.size()]);

    Arrays.sort(ba, (b1, b2) ->
    XBitSet.cardinalityComparator.compare(b1.vertices, b2.vertices));

    for (Block block: ba) {
      block.evaluate();
    }
    if (whole.value != null && 
        (opt == null || whole.value.compareTo(opt) < 0)) {
      opt = whole.value;
    }
  }

  public void improve(int budget) {
    assert opt != null;
    this.budget = budget;
    nTicks = 0;
    
    subfeasiblesSieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      subfeasiblesSieve[v] = new SubblockSieve(g, opt.width + 1);
    }
    
    queue = new PriorityQueue<>();
    
    for (Block block: blockMap.values()) {
      if (block.value != null &&
          block.value.compareTo(opt) < 0) {
        queue.add(block);
        int v0 = block.vertices.nextSetBit(0);
        subfeasiblesSieve[v0].add(block.vertices, block.separator);
      }
    }
    
    while (!queue.isEmpty() && nTicks < budget) {
      Block toProcess = queue.remove();
      if (TRACE) {
        System.out.println("toProcess " + toProcess);
        System.out.println(queue.size() + " in queue " + blockMap.size() + " blocks " +
            + pmcMap.size() + " pmcs" + " " + numberOfSubfeasibles() + " subfeasibles");
      }    
      toProcess.process();
    }
    doDP();
  }
  
  int numberOfSubfeasibles() {
    int count = 0;
    for (Block block: blockMap.values()) {
      if (block.value != null && block.value.compareTo(opt) < 0) {
        count++;
      }
    }
    return count;
  }
  
  public TreeDecomposition getTD() {
    TreeDecomposition td = new TreeDecomposition(0, 0, g);
    whole.fillTD(td);
    return td;
  }
      
     
  public Set<XBitSet> conducives(int nConducives) {
    Set<XBitSet> result = new HashSet<> ();
    for (PMC pmc: pmcMap.values()) {
      if (result.contains(pmc.separator)) {
        continue;
      }
      if (pmc.valueFor(g.all).equals(opt)) {
        pmc.collectConducives(result);
      }
      if (result.size() > nConducives) {
        return result;
      }
    }
    return result;
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
      if (newBlocks != null) {
        newBlocks.add(f);
      }
    }
    return f;
  }
  
  class Block implements Comparable<Block> {
    XBitSet vertices;
    XBitSet separator;
    boolean queued;
    boolean processed;
    Value value;
    Set<PMC> caps;
    Set<PMC> waiters;
    
    Block(XBitSet vertices) {
      this(vertices, g.neighborSet(vertices));
    }

    Block(XBitSet vertices, XBitSet separator) {
      this.vertices = vertices;
      this.separator = separator;
    }
   
    void evaluate() {
      if (TRACE_DP) {
        System.out.println("evaluating " + this);
      }
      int n = vertices.unionWith(separator).cardinality();
      value = new Value(n - 1, 1);
      if (caps != null) {
        for (PMC cap: caps) {
           Value val = cap.valueFor(vertices);
           if (val != null && val.compareTo(value) < 0) {
             value = val;
           }
        }
      }
      if (TRACE_DP) {
        System.out.println("evaluated " + this);
      }

    }

    void process() {
      newBlocks = new HashSet<>();
      XBitSet rest = g.all.subtract(vertices).subtract(separator);
      search(rest, separator);
      Block[] ba = newBlocks.toArray(new Block[newBlocks.size()]);
      Arrays.sort(ba, (b1, b2) ->
          XBitSet.cardinalityComparator.compare(b1.vertices, b2.vertices));
      for (Block block: ba) {
        assert block.separator.cardinality() <= opt.width;
        Value oldVal = block.value;
        block.evaluate();
        if (oldVal == null && block.value.compareTo(value) < 0) {
          int v0 = block.vertices.nextSetBit(0);
          subfeasiblesSieve[v0].add(block.vertices, block.separator);
          queue.add(block);
        }
      }
      processed = true;
    }
    
    void search(XBitSet scope, XBitSet sep) {
      nTicks++;
      if (nTicks > budget) {
        return;
      }
      assert sep.cardinality() <= opt.width;
      
      int v0 = scope.nextSetBit(0);
      ArrayList<XBitSet> candidates = subfeasiblesSieve[v0].get(scope, sep);
      
      for (XBitSet cand: candidates) {
        assert cand.isSubset(scope);
        XBitSet candSep = g.neighborSet(cand);
        XBitSet rest = scope.subtract(cand).subtract(candSep);
        XBitSet unionSep = sep.unionWith(candSep);
        assert unionSep.cardinality() <= opt.width + 1:
          opt + " " + sep + " " + candSep + " " + unionSep;
        tryUnion(rest, unionSep);
      }
      
      if (sep.cardinality() <= opt.width) {
        tryUnion(scope.removeBit(v0), sep.addBit(v0));
      }
    }

    void tryUnion(XBitSet rest, XBitSet unionSep) {
      ArrayList<XBitSet> components = g.componentsOf(rest);
      ArrayList<XBitSet> fulls = new ArrayList<>();
      for (XBitSet compo: components) {
        if (g.neighborSet(compo).equals(unionSep)) {
          fulls.add(compo);
        }
        else {
          Block block = makeBlock(compo);
          if (block.value == null) {
            LocalGraph local = block.localGraph();
            TreeDecomposition td = greedyDecomposition(local.h);
            if (td.width < opt.width) {
              for (XBitSet bag: td.setOfBags()) {
                XBitSet pmc = bag.convert(local.inv);
                makePMC(pmc);
              }
            }
          }
        }
      }
      
      if (fulls.isEmpty()) {
        if (g.isPMC(unionSep)) {
          PMC p = makePMC(unionSep);
          if (TRACE) {
            System.out.println("pmc created " + p);
          }
        }
      }
      else if (fulls.size() == 1 && unionSep.cardinality() <= opt.width) {
        search(fulls.get(0), unionSep);
      }
    }
    
    LocalGraph localGraph() {
      return new LocalGraph(g, vertices.unionWith(separator));
    }

    void addCap(PMC cap) {
      if (TRACE_DP) {
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
        LocalGraph local = localGraph();
        TreeDecomposition td1 = greedyDecomposition(local.h);
        int r = findBagContaining(td1, separator.convert(local.conv));
        return fillTDFromTD(td1, r, 0, local.inv, td);
      }
      int b = td.addBag(cap.separator.toArray());
      for (Block f: cap.blocks) {
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
      Value valueBest = null;
      for (PMC cap: caps) {
        Value val = cap.valueFor(this.vertices);
        if (valueBest == null || val.compareTo(valueBest) < 0) {
          best = cap;
          valueBest = val;
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
      int c = XBitSet.cardinalityComparator.compare(vertices, f.vertices);
      if (c != 0) {
        return -c;
      }
      return value.compareTo(f.value);  
    }
    
    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("Block: separator " + separator + " vertices " + vertices + 
          " value " + value);
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
      return 2 * vertices.cardinality() + separator.cardinality() <= g.n;
    }
  }
  
  class PMC {
    XBitSet separator;
    Block[] blocks;
    
    PMC(XBitSet separator) {
      this.separator = separator;
      ArrayList<XBitSet> components = g.separatedComponents(separator);
      components.sort(XBitSet.cardinalityComparator);
      blocks = new Block[components.size()];
      int i = 0;
      for (XBitSet compo: components) {
        blocks[i++] = makeBlock(compo);
      }
    }

    void registerAsCap() {
      for (Block block: innerBlocks()) {
        assert block != null;
        block.addCap(this);
      }
      if (allBlocksSmall()) {
        whole.addCap(this);
      }
    }
    
    boolean allBlocksSmall() {
      for (Block block: blocks) {
        if (!block.isSmall()) {
          return false;
        }
      }
      return true;
    }
    
    Set<Block> innerBlocks() {
      Set<Block> result = new HashSet<>();
      for (Block block: blocks) {
        Block theOther = block.theOtherBlock(separator);
        assert theOther != null;
        result.add(theOther);
      }
      return result;
    }

    void collectConducives(Set<XBitSet> result) {
      if (result.contains(separator)) {
        return;
      }
      result.add(separator);
      for (Block f: blocks) {
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

    Value valueFor(XBitSet component) {
//      System.out.println("value for " + component + " " + this);
      Value val = new Value(separator.cardinality() - 1, 1);
//      System.out.println("initial value " + val);
      for (Block f: blocks) {
        if (f.vertices.isSubset(component)) {
//          System.out.println(" block " + f);
          if (f.value == null) {
            return null;
          }
          val.add(f.value);
//          System.out.println("value now " + val);
        }
      }
      return val;
    }
    
    @Override
    public String toString() {
      return "pmc " + separator + " " + blocks.length + " blocks";
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

    
  static void test(String group, String name, int budget) {
    File file = new File("../instance/" + group + "/" + name + ".gr");
    Graph g0 = Graph.readGraph(file);
    System.out.println("graph read: " + file.getPath() + ", n = " + g0.n + ",  m =" + g0.numberOfEdges());
    System.out.println("isConnected " + g0.isConnected(g0.all));
    ArrayList<XBitSet> components = g0.componentsOf(g0.all);
    
    XBitSet compo = XBitSet.largest(components);
    
    System.out.println("largest " + compo);
    
    Subgraph sub = new Subgraph(g0, compo);
    
    Graph g = sub.h;
    long t0 = System.currentTimeMillis();
    PIDImprover pidImp = new PIDImprover(g);
    
    TreeDecomposition td = greedyDecomposition(g);
    System.out.println("greedy width " + td.width + " " + 
        (System.currentTimeMillis() - t0) + " millisecs");

    pidImp.importPMCs(td.setOfBags());
    System.out.println("initial value " + pidImp.opt + " " + 
        (System.currentTimeMillis() - t0) + " millisecs");

    while (true) {
      Value val = pidImp.opt;
      pidImp.improve(budget);
      if (pidImp.opt.equals(val)) {
        break;
      }
      val = pidImp.opt;
      System.out.println("new value " + val + " " + 
          (System.currentTimeMillis() - t0) + " millisecs");
    }
    
    td = pidImp.getTD();
    System.out.println("final width " + td.width);
    td.validate();
    
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
    test("pace17exact", "ex167", 1000);
//    test("grid", "troidal4_4", 1000);
//    test("grid", "troidal5_5", 1000);
//    test("grid", "troidal6_6", 1000);
//    test("grid", "troidal7_7", 1000);
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
    
    
  }

}
