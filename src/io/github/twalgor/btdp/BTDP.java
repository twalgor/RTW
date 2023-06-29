package io.github.twalgor.btdp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
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
import io.github.twalgor.log.Log;
import io.github.twalgor.minseps.MinSepsGenerator;

public class BTDP {
//static final boolean TRACE = true;
  static final boolean TRACE = false;
//    static final boolean TRACE_DP = true;
  static final boolean TRACE_DP = false;
  
  static final double MAX_INDENT = 50;
  static final int N_TRY = 10;
  
  static final int VERSION = 2;
  static final int CONDUCIVES_MAX = 200;

  public static Log log;

  Graph g;
  public Value value;

  public Set<XBitSet> pmcs;

  public Map<XBitSet, Block> blockMap;
  Map<XBitSet, PMC> pmcMap;
  Block[] ba;
  int dpMax;

  public BTDP(Graph g, Set<XBitSet> pmcs) {
    this.g = g;
    this.pmcs = pmcs;
  }

  public void importPMCs(Set<XBitSet> pmcs) {
    this.pmcs.addAll(pmcs);
  }
  
  public Set<Block> feasibleBlocks(int k) {
    Set<Block> blocks = new HashSet<>();
    for (Block block: blockMap.values()) {
      assert !block.separator.isEmpty();
      if (block.value.width <= k) {
        blocks.add(block);
      }
    }
    return blocks;
  }
  
  public Set<XBitSet> safeSeparators() {
    Set<XBitSet> seps = new HashSet<>();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.value.width == value.width) {
        for (Block block: pmc.subblock) {
          seps.add(block.separator);
        }
      }
    }
    return seps;
  }
  
  public void doDP() {
    value = dp();
  }
  
  public Set<XBitSet> enrich(int dpMax) {
    this.dpMax = dpMax;
    doDP();
    PMC root = largestConducive();
    XBitSet vs = root.enlarge();
    LocalGraph lg = new LocalGraph(g, vs);
    Set<XBitSet> localPMCs = generateConducives(lg.h, value.width);
    Set<XBitSet> pmcs = conducives();
    pmcs.addAll(XBitSet.convertAll(localPMCs, lg.inv));
    return pmcs;
  }
  
  Set<XBitSet> generateConducives(Graph h, int k) {
    MinSepsGenerator msg = new MinSepsGenerator(h, k);
    msg.generate();
    Set<XBitSet> minSeps = msg.minSeps;
    Set<XBitSet> conducives = new HashSet<>();
  
    boolean moving = true;
    while (moving && conducives.size() < CONDUCIVES_MAX) {
      moving = false;
      int nc = conducives.size();
      SemiPID spid = new SemiPID(h, k, minSeps, false);
      TreeDecomposition td = spid.decompose();
      if (td == null) {
        return conducives;
      }
      td = minimalize(td);
      conducives.addAll(td.setOfBags());
      moving = conducives.size() > nc;
      XBitSet sep = mostBalancedMinSep(td);
      minSeps.remove(sep);
    }
    return conducives;
  }

  XBitSet mostBalancedMinSep(TreeDecomposition td) {
    XBitSet best = null;
    int lcBest = 0;
    for (XBitSet sep: minSepsFrom(td)) {
      int lc = largestCompoSize(sep, td.g);
      if (best == null || 
          lc < lcBest) {
        lcBest = lc;
        best = sep;
      }
    }
    return best;
  }
  
  Set<XBitSet> minSepsFrom(TreeDecomposition td) {
    Set<XBitSet> minSeps = new HashSet<>();
    for (int b = 1; b <= td.nb; b++) {
      XBitSet bag = new XBitSet(td.bags[b]);
      for (int i = 0; i < td.degree[b]; i++) {
        int b1 = td.neighbor[b][i];
        if (b < b1) {
          XBitSet sep = bag.intersectWith(new XBitSet(td.bags[b1]));
          if (td.g.isMinimalSeparator(sep)) {
            minSeps.add(sep);
          }
        }
      }
    }
    return minSeps;
  }
  
  int largestCompoSize(XBitSet sep, Graph g) {
    ArrayList<XBitSet> components = g.separatedComponents(sep);
    return XBitSet.largest(components).cardinality();
  }
  
  private PMC largestConducive() {
    PMC largest = null;
    for (PMC pmc: pmcMap.values()) {
      if (pmc.value.compareTo(value) > 0) {
        continue;
      }
      if (largest == null || pmc.vertices.cardinality() > largest.vertices.cardinality()) {
        largest = pmc;
      }
    }
    return largest;
  }

  PMC aRootPMC(Value value) {
    for (PMC pmc : pmcMap.values()) {
      if (pmc.value.equals(value)) {
        return pmc;
      }
    }
    return null;
  }
  
  Set<XBitSet> balancedConducives() {
    Set<XBitSet> result = new HashSet<>();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.value.equals(value) &&
          pmc.allBlocksSmall()) {
        result.add(pmc.vertices);
      }
    }
    return result;
  }

  public void mergeWith(BTDP side) {
    
  }
  
  void mergeWith(BTDP side, int dpMax) {
    this.dpMax = dpMax;
    if (TRACE) {
      System.out.println("merging " + value + "(" +
          + pmcs.size() + " pmcs), with " + side.value + 
          "(" + side.pmcs.size() + " pmcs)");
      assert !blockMap.isEmpty();
      assert !side.blockMap.isEmpty();
    }
    Set<XBitSet> sConducives = side.conducives();
    ArrayList<XBitSet> largestConducives = new ArrayList<>();
    for (XBitSet pmc: sConducives) {
      if (pmc.cardinality() == side.value.width + 1) {
        largestConducives.add(pmc);
      }
    }
    
    Set<XBitSet> toAdd = new HashSet<>();
    for (XBitSet bag: largestConducives) {
      for (PMC pmc1: pmcMap.values()) {
        if (pmc1.vertices.intersects(bag)) {
          toAdd.addAll(pmcsFrom(pmc1.vertices.unionWith(bag), side));
        }
      }
    }
    pmcs.addAll(sConducives);
    XBitSet[] ta = new XBitSet[toAdd.size()];
    toAdd.toArray(ta);
    Arrays.sort(ta, (s1, s2) -> -(s1.cardinality() - s2.cardinality()));
    ta = Arrays.copyOf(ta, Math.min(ta.length, N_TRY));
    for (XBitSet bag: ta) {
      if (g.isPMC(bag)) {
        pmcs.add(bag);  
      }
    }
    value = dp();
  }

  Set<XBitSet> pmcsFrom(XBitSet bag, BTDP side) {
    Set<XBitSet> pmcs = new HashSet<>();
    LocalGraph lg = new LocalGraph(g, bag);
    TreeDecomposition td = SemiPID.decompose(lg.h);
    if (td.width > bag.cardinality() - 1) { 
      return pmcs;
    }
    td = minimalize(td);
    pmcs.addAll(XBitSet.convertAll(td.setOfBags(), lg.inv));
    ArrayList<XBitSet> components = g.separatedComponents(bag);
    for (XBitSet compo: components) {
      if (blockMap.get(compo) == null &&
          side.blockMap.get(compo) == null) {
        pmcs.addAll(pmcsFromComponent(compo));
      }
    }
    return pmcs;
  }
  
  Set<XBitSet> pmcsFromComponent(XBitSet compo) {
    XBitSet vs = g.closedNeighborSet(compo);
    XBitSet sep = vs.subtract(compo);
    Subgraph sub = new Subgraph(g, vs);
    sub.h.fill(sep.convert(sub.conv));
    TreeDecomposition td = decompose(sub.h);
    return XBitSet.convertAll(td.setOfBags(), sub.inv);
  }

  TreeDecomposition decompose(Graph h) {
    if (h.n <= dpMax) {
      TreeDecomposition td = SemiPID.decompose(h);
      td = minimalize(td);
      return td;
    }
    else {
      Graph f = h.copy();
      MMAF mmaf = new MMAF(f);
      mmaf.triangulate();
      TreeDecomposition td = Chordal.chordalToTD(f);
      td.g = h;
      return td;
    }
  }

  TreeDecomposition minimalize(TreeDecomposition td) {
    MinimalizeTD mtd = new MinimalizeTD(td.g, td);
    return mtd.minimalize();
  }
  
  public void filter() {
    if (TRACE) {
      System.out.println("filtering " + blockMap.size() + " blocks and " + pmcMap.size() + " pmcs");
    }
    Set<XBitSet> pmcsToKeep = new HashSet<>();

    for (PMC pmc : pmcMap.values()) {
      if (pmc.almostAllFeasible(value)) {
        pmcsToKeep.add(pmc.vertices);
      }
    }
    pmcMap.clear();
    blockMap.clear();
    
    pmcs = pmcsToKeep;
    value = dp();

  }
  
  public void filterOld() {
    if (TRACE) {
      System.out.println("filtering " + blockMap.size() + " blocks and " + pmcMap.size() + " pmcs");
    }
    Set<XBitSet> pmcsToKeep = new HashSet<>();

    for (PMC pmc : pmcMap.values()) {
      if (pmc.value.compareTo(value) <= 0) {
        pmcsToKeep.add(pmc.vertices);
      }
    }
    pmcMap.clear();
    blockMap.clear();
    
    pmcs = pmcsToKeep;
    value = dp();
  }
  
  Value dp() {
    if (TRACE_DP) {
      System.out.println("dp ...");
    }
    blockMap = new HashMap<>();
    pmcMap = new HashMap<>();

    for (XBitSet pmc: pmcs) {
      makePMC(pmc);
    }
    if (TRACE) {
      System.out.println("basic generation " + blockMap.size() + " blocks, " + 
          pmcMap.size() + " pmcs");
    }

    Block[] ba = new Block[blockMap.size()];
    blockMap.values().toArray(ba);

    for (Block block: ba) {
      if (block.caps.isEmpty() && 
          (value == null || 
            block.component.cardinality() + block.separator.cardinality() < value.width + 1)) {
        Subgraph sub = new Subgraph(g, block.component.unionWith(block.separator));
        sub.h.fill(block.separator.convert(sub.conv));
        MMAF mmaf = new MMAF(sub.h);
        mmaf.triangulate();
        Chordal chordal = new Chordal(sub.h);
        for (XBitSet clique: chordal.maximalCliques()) {
          XBitSet bag = clique.convert(sub.inv);
          assert g.isPMC(bag);
          makePMC(bag);
        }
      }
    }
    if (TRACE) {
      System.out.println("after completion " + blockMap.size() + " blocks, " + 
          pmcMap.size() + " pmcs");
    }
    return dpMain();
  }
  
  Value dpMain() {
    ba = new Block[blockMap.size()];
    blockMap.values().toArray(ba);
    Arrays.sort(ba);

    for (Block block : ba) {
      block.evaluate();
    }

    for (PMC pmc : pmcMap.values()) {
      pmc.computeValue();
    }

    Value val = new Value(g.n - 1, 1);
    for (PMC pmc : pmcMap.values()) {
      if (pmc.value.compareTo(val) <= 0) {
        val = pmc.value;
      }
    }

    return val;
  }
  
  public Set<XBitSet> conducives() {
    Set<XBitSet> conducives = new HashSet<>();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.value.equals(value)) {
        conducives.add(pmc.vertices);
      }
    }
    return conducives;
  }

  public Set<PMC> conducivePMCs() {
    Set<PMC> conducives = new HashSet<>();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.value.equals(value)) {
        conducives.add(pmc);
      }
    }
    return conducives;
  }
  
  public void prune(int maxPMCs) {
    Set<XBitSet> pmcsChosen = new HashSet<>();
    PMC[] pmca = pmcMap.values().toArray(new PMC[pmcMap.size()]);
    Arrays.sort(pmca, (p1, p2) -> 
      -XBitSet.cardinalityComparator.compare(p1.vertices, p2.vertices));
    for (PMC p: pmca) {
      if (pmcsChosen.contains(p.vertices)) {
        continue;
      }
      TreeDecomposition td = new TreeDecomposition(0, 0, g);
      p.fillDecomposition(g.all, td);
      Set<XBitSet> pmcs1 = td.setOfBags();
      pmcsChosen.addAll(pmcs1);
//      System.out.println(pmcsChosen.size() + " pmcs chosen");
      if (pmcsChosen.size() > maxPMCs) {
        break;
      }
    }
    pmcs = pmcsChosen;
    value = dp();
  }

  ArrayList<TreeDecomposition> decompositions(int nd) {
    Value val = dp();
    int k = val.width;
    return decompositions(nd, k);
  }
  
  ArrayList<TreeDecomposition> decompositions(int nd, int k) {
    ArrayList<TreeDecomposition> decompos = new ArrayList<>();
    value = dp();
    int width = value.width;
    if (width > k) {
      return decompos;
    }
    Set<XBitSet> pmcsBak = new HashSet<>(pmcs);
    for (int i = 0; i < nd; i++) {
      if (value.width > width) {
        break;
      }
      TreeDecomposition td = extractTD(value);
      if (td == null) {
        break;
      }
      decompos.add(td);
      XBitSet bag = aLargestBag(td);
      pmcs.remove(bag);
      value = dp();
    }
    pmcs = pmcsBak;
    return decompos;
  }
  
  private XBitSet aLargestBag(TreeDecomposition td) {
    XBitSet largest = null;
    for (int b = 1; b <= td.nb; b++) {
      if (largest == null || td.bags[b].length < largest.cardinality()) {
        largest = new XBitSet(td.bags[b]);
      }
    }
    return largest;
  }

  public TreeDecomposition aDecomposition() {
    value = dp();
    System.out.println("value " + value);
    return extractTD(value);
  }
  
  TreeDecomposition extractTD(Value value) {
    for (PMC pmc : pmcMap.values()) {
//      System.out.println("pmc.value " + pmc.value);

      if (pmc.value.equals(value)) {
        TreeDecomposition td = new TreeDecomposition(0, 0, g);
        pmc.fillDecomposition(g.all, td);
//        System.out.println("returning td with width " + td.width);
        return td;
      }
    }
    return null;
  }

  Set<XBitSet> localConducives(XBitSet component, XBitSet separator, int k) {
    assert separator.cardinality() <= k;
    XBitSet closure = component.unionWith(separator);
    Subgraph sub = new Subgraph(g, closure);
    sub.h.fill(separator.convert(sub.conv));
    Set<XBitSet> localPMCs = new HashSet<>();
    for (PMC pmc: pmcMap.values()) {
      if (pmc.vertices.isSubset(closure)) {
        localPMCs.add(pmc.vertices.convert(sub.conv));
      }
    }
    BTDP btdp = new BTDP(sub.h, localPMCs);
    btdp.doDP();
    
    Set<XBitSet> conducives = new HashSet<>();
    for (XBitSet bag: btdp.conducives()) {
      XBitSet bag1 = bag.convert(sub.inv);
      conducives.add(bag1);
    }
    return conducives;
  }

  XBitSet anotherFull(XBitSet separator, XBitSet component) {
    ArrayList<XBitSet> fulls = g.fullComponents(separator);
    assert fulls.size() >= 2;
    for (XBitSet full: fulls) {
      if (!full.equals(component)) {
        return full;
      }
    }
    return null;
  }

  Block makeBlock(XBitSet component) {
    // ensures that a block for a component is unique
    // thus, the equality for blocks is the identity
    assert !component.isEmpty();
    Block block = blockMap.get(component);
    if (block == null) {
      block = new Block(component);
      assert g.fullComponents(block.separator).size() >= 2;
      blockMap.put(component, block);
    }
    return block;
  }

  PMC makePMC(XBitSet separator) {
    // ensures that a bag for a vertex set is unique
    // thus, the equality for bags is the identity
    PMC pmc = pmcMap.get(separator);
    if (pmc == null) {
      pmc = new PMC(separator);
      pmcMap.put(separator, pmc);
    }
    return pmc;
  }

  boolean allFeasible(XBitSet separator) {
    ArrayList<XBitSet> components = g.separatedComponents(separator);
    for (XBitSet compo : components) {
      Block b = blockMap.get(compo);
      assert b != null;
      if (!b.isFeasible()) {
        return false;
      }
    }
    return true;
  }

  String indent(int d) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < d; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  static int indexOf(Object x, Object[] a) {
    for (int i = 0; i < a.length; i++) {
      if (x == a[i]) {
        return i;
      }
    }
    return 0;
  }

  String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  public class Block implements Comparable<Block> {
    public XBitSet component;
    public XBitSet separator;
    Set<PMC> caps;
    public Value value;

    Block(XBitSet component) {
      this.component = component;
      separator = g.neighborSet(component);
      caps = new HashSet<PMC>();
    }

    boolean isAntiFeasible() {
      ArrayList<XBitSet> components = g.separatedComponents(separator);
      for (XBitSet compo: components) {
        if (compo.equals(component)) {
          continue;
        }
        Block block = blockMap.get(compo);
        if (block == null) {
          return false;
        }
        if (block.value == null) {
          return false;
        }
        if (block.value.width >= value.width) {
          return false;
        }
      }
      return true;
    }

    XBitSet union() {
      return component.unionWith(separator); 
    }

    int fillDecomposition(TreeDecomposition td) {
      PMC bestCap = bestCap();

      if (bestCap != null) {
        return bestCap.fillDecomposition(component, td);
      } 
      else {
        XBitSet cn = g.closedNeighborSet(component);
        assert cn.cardinality() <= BTDP.this.value.width + 1: cn;
        return td.addBag(cn.toArray());
      }
    }

    public PMC bestCap() {
      Value best = new Value(g.n, 1);
      PMC bestCap = null;
      for (PMC cap : caps) {
        Value val = cap.valueFor(component); 
        if (val.compareTo(best) < 0) {
          bestCap = cap;
          best = val;
        }
      }
      return bestCap;
    }

    void evaluate() {
      if (TRACE_DP) {
        System.out.println(indent() + "evaluating " + this);
      }
      if (caps.isEmpty()) {
        value = new Value(component.cardinality() + separator.cardinality() - 1, 1);
        return;
      }
      int w = component.cardinality() + separator.cardinality() - 1;
      value = new Value(w, 1);
      for (PMC pmc : caps) {
        Value val = pmc.valueFor(component);
        if (val.compareTo(value) < 0) {
          value = val;
        }
      }
      if (TRACE_DP) {
        System.out.println(indent() + "value = " + value);
      }
    }

    boolean isFeasible() {
      return value.width <= BTDP.this.value.width;
    }

    boolean addCap(PMC bag) {
      if (caps.contains(bag)) {
        return false;
      }
      caps.add(bag);
      return true;
    }

    Set<XBitSet> localConducives(XBitSet component, XBitSet separator, int k) {
      assert separator.cardinality() <= k;
      XBitSet closure = component.unionWith(separator);
      Set<XBitSet> localPMCs = new HashSet<>();
      for (PMC pmc: pmcMap.values()) {
        if (pmc.vertices.isSubset(closure)) {
          localPMCs.add(pmc.vertices);
        }
      }
      blockMap = new HashMap<>();
      pmcMap = new HashMap<>();
      
      for (XBitSet bag: localPMCs) {
        makePMC(bag);
      }
      
      XBitSet full = anotherFull(separator, component);
      Block externalBlock = blockMap.get(full);
      assert externalBlock != null;
      externalBlock.value = new Value(separator.cardinality(), 1);
      dp();
      
      PMC best = null;
      for (PMC pmc: pmcMap.values()) {
        if (best == null || pmc.value.compareTo(best.value) < 0) {
          best = pmc;
        }
      }
      Value val = best.value;
      assert val.width <= k;
      
      Set<XBitSet> conducives = new HashSet<>();
      for (PMC pmc: pmcMap.values()) {
        if (pmc.value.equals(val)) {
          conducives.add(pmc.vertices);
        }
      }
      return conducives;
    }

    XBitSet anotherFull(XBitSet separator, XBitSet component) {
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      assert fulls.size() >= 2;
      for (XBitSet full: fulls) {
        if (!full.equals(component)) {
          return full;
        }
      }
      return null;
    }

    Block theOtherBlock() {
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      assert fulls.size() >= 2;
      for (XBitSet full : fulls) {
        if (!full.equals(component)) {
          return makeBlock(full);
        }
      }
      assert false;
      return null;
    }

    boolean isFullComponent(XBitSet component, XBitSet sep) {
      for (int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
        if (component.isDisjoint(g.neighborSet[v])) {
          return false;
        }
      }
      return true;
    }

    String indent() {
      double logN = Math.log(g.n);
      double logS = Math.log(component.cardinality());
      return BTDP.this.indent((int) ((double) MAX_INDENT * (logN - logS) / logN));
    }

    @Override
    public int compareTo(Block s) {
      return XBitSet.cardinalityComparator.compare(component, s.component);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("component = " + component);
      sb.append(", separator = " + separator);
      sb.append(", " + caps.size() + " caps");
      sb.append(", width = " + value);
      if (BTDP.this.value != null) {
        sb.append(" isFeasible = " + isFeasible());
      }
      return sb.toString();
    }

    void dump() {
      System.out.println(indent() + this);
      for (PMC cap : caps) {
        cap.dump(this);
      }
    }

    ArrayList<Block> otherBlocks() {
      ArrayList<XBitSet> components = g.separatedComponents(component.unionWith(separator));
      XBitSet full = null;
      for (XBitSet compo : components) {
        if (g.neighborSet(compo).equals(separator)) {
          full = compo;
          break;
        }
      }
      assert full != null;

      ArrayList<Block> result = new ArrayList<>();
      result.add(makeBlock(full));

      for (XBitSet compo : components) {
        if (compo != full) {
          result.add(makeBlock(compo));
        }
      }
      return result;
    }

    int fillTD(TreeDecomposition td, int[] conv) {
      PMC cap = bestCap();
      if (cap == null) {
        return -1;
      }
      int r = td.addBag(cap.vertices.convert(conv).toArray());
      for (Block block : cap.subblock) {
        if (block.component.isSubset(component)) {
          int b = block.fillTD(td, conv);
          if (b == -1) {
            return -1;
          }
          td.addEdge(r, b);
        }
      }
      return r;
    }

    void collectBags(Set<PMC> collected) {
      PMC cap = bestCap();
      if (cap == null) {
        return;
      }
      collected.add(cap);
      for (Block block : cap.subblock) {
        if (block.component.isSubset(component)) {
          block.collectBags(collected);
        }
      }
    }

    public Set<XBitSet> supportingPMCs() {
      Set<XBitSet> pmcs = new HashSet<>();
      supportingPMCs(pmcs);
      return pmcs;
    }
    
    void supportingPMCs(Set<XBitSet> pmcs) {
      PMC cap = bestCap();
      cap.supportingPMCs(component, pmcs);
    }
  }

  
  public class PMC {
    public XBitSet vertices;
    public Block[] subblock;
    Value value;
    Value directedValue;
    boolean mark;

    PMC(XBitSet vertices) {
      super();
      //      assertPMC(separator);

      this.vertices = vertices;
      assert g != null;
      assert g.isPMC(vertices);
      ArrayList<XBitSet> components = g.separatedComponents(vertices);
      subblock = new Block[components.size()];
      for (int i = 0; i < subblock.length; i++) {
        XBitSet compo = components.get(i);
        subblock[i] = makeBlock(compo);
      }

      for (Block block : subblock) {
        XBitSet sep = block.separator;
        XBitSet component = vertices.subtract(sep);
        XBitSet nb = g.neighborSet(component);
        for (Block b : subblock) {
          if (b.component.intersects(nb)) {
            component.or(b.component);
          }
        }
        assert g.neighborSet(component).equals(sep);
        Block superblock = makeBlock(component);
        superblock.addCap(this);
      }
    }

    boolean almostAllFeasible(Value val) {
      int count = 0;
      for (Block block: subblock) {
        if (block.value.compareTo(val) > 0) {
          count++;
        }
      }
      return count <= 1;
    }

    void supportingPMCs(XBitSet component, Set<XBitSet> pmcs) {
      pmcs.add(vertices);
      for (Block block: subblock) {
        if (block.component.isSubset(component)) {
          block.supportingPMCs(pmcs);
        }
      }
    }

    public XBitSet enlarge() {
      XBitSet vs = vertices;
      Set<Block> blocks = new HashSet<>();
      for (Block block: subblock) {
        blocks.add(block);
      }
      
      while (!blocks.isEmpty()) {
        Block block = remove(blocks);
        assert block != null;
        PMC cap = block.bestCap();
        assert cap != null;
        XBitSet vs1 = vs.unionWith(cap.vertices);
        if (vs1.cardinality() > dpMax) {
          return vs;
        }
        vs = vs1;
        for (Block b: cap.subblock) {
          if (b.component.isSubset(block.component)) {
            blocks.add(b);
          }
        }
      }
      return vs;
    }
    
    Block remove(Set<Block> blocks) {
      Block block = null;
      for (Block b: blocks) {
        block = b;
        break;
      }
      blocks.remove(block);
      return block;
    }

    boolean allBlocksSmall() {
      for (Block block: subblock) {
        if (block.component.cardinality() > g.n / 2) {
          return false;
        }
      }
      return true;
    }

    boolean allFeasible() {
      for (Block block: subblock) {
        if (block.value.compareTo(value) > 0) {
          return false;
        }
      }
      return true;
    }

    void computeValue() {
      int w = vertices.cardinality() - 1;
      value = new Value(w, 1);
      for (Block block : subblock) {
        value.add(block.value);
      }
    }
    
    Value valueFor(XBitSet component) {
      int w = vertices.cardinality() - 1;
      Value val = new Value(w, 1);
      for (Block block : subblock) {
        if (block.component.isSubset(component)) {
          val.add(block.value);
        }
      }
      return val;
    }

    boolean isFeasible() {
      return value.compareTo(BTDP.this.value) <= 0;
    }

    int fillDecomposition(XBitSet component, TreeDecomposition td) {
      int r = td.addBag(vertices.toArray());
      for (Block block : subblock) {
        if (block.component.isSubset(component)) {
          int b = block.fillDecomposition(td);
          td.addEdge(r, b);
        }
      }
      return r;
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("separator = " + vertices.toString().substring(0, 100));
      sb.append("\n");
      sb.append("value = " + value + ", " + subblock.length + " subblocks:");
      for (Block block : subblock) {
        sb.append(" " + block.component.cardinality());
      }
      return sb.toString();
    }

    void dump(Block parent) {
      System.out.println(parent.indent() + "p:" + this);
      for (Block block : subblock) {
        if (block.component.isSubset(parent.component)) {
          block.dump();
        }
      }
    }
  }
  
  void printState(String prefix) {
    System.out.println(prefix + value + ", " + blockMap.size() + ", " + pmcMap.size());
  }

  static void log(String message) {
    if (log != null) {
      log.log(message, true);
    } else {
      System.out.println(message);
    }
  }

  public Set<XBitSet> cores(int i) {
    // TODO Auto-generated method stub
    return null;
  }

  public Set<XBitSet> minSeps() {
    Set<XBitSet> minSeps = new HashSet<>(); 
    for (Block block: blockMap.values()) {
      minSeps.add(block.separator);
    }
    return minSeps;
  }

}

