package io.github.twalgor.recursive;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import io.github.twalgor.btdp.Value;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;

public class ContractionBT {
//  static boolean TRACE = true;
static boolean TRACE = false;
//static boolean TRACE_DP = true;
  static boolean TRACE_DP = false;
  Graph g;
  Minor minor;
  
  Graph h;
  
  
  boolean improved;
  boolean exhausted;

  Map<XBitSet, Block> blocksMap;
  Map<XBitSet, PMC> pmcsMap;

  Queue<Block> queue;

  Value btValue;
  Set<XBitSet> usedPMCs;

  public ContractionBT(Graph g, Minor minor, Set<XBitSet> pmcs) {
    this.g = g;
    this.minor = minor;
    h = minor.getGraph();
    blocksMap = new HashMap<>();
    pmcsMap = new HashMap<>();
    for (XBitSet pmc: pmcs) {
      makePMC(pmc);
    }
  }
  
  public TreeDecomposition firstTD() {
    btDP();
    usedPMCs = new HashSet<>();
    for (PMC p: pmcsMap.values()) {
      if (p.valueFor(g.all).equals(btValue)) {
        TreeDecomposition td = p.getUncontractedTD();
        for (XBitSet pmc: td.setOfBags()) {
          assert weightOf(pmc) <= btValue.width + 1;
          usedPMCs.add(pmc);
        }
        contractTD(td, minor);
        return td;
      }
    }
    assert false;
    return null;
  }
  
  public TreeDecomposition anotherTD() {
    for (PMC p: pmcsMap.values()) {
      if (p.valueFor(g.all).equals(btValue) &&
          !usedPMCs.contains(p.separator)) {
        TreeDecomposition td = p.getUncontractedTD();
        for (XBitSet pmc: td.setOfBags()) {
          usedPMCs.add(pmc);
        }
        contractTD(td, minor);
        return td;
      }
    }
    return null;
  }

  
  void contractTD(TreeDecomposition td, Minor minor) {
    for (int b = 1; b <= td.nb; b++) {
      XBitSet bag = new XBitSet(td.bags[b]);
      td.bags[b] = bag.convert(minor.map).toArray();
    }
    td.g = minor.getGraph();
    td.width = 0;
    for (int b = 1; b <= td.nb; b++) {
      if (td.bags[b].length > td.width + 1) {
        td.width = td.bags[b].length - 1;
      }
    }
  }

  public void btDP() {
    Block[] fa = blocksMap.values().toArray(new Block[blocksMap.size()]);
    Arrays.sort(fa);

    for (Block f: fa) {
      if (TRACE_DP) {
        System.out.println("evaluating " + f);
      }
      f.evaluate();
    }
    
    btValue = new Value(g.n - 1, 1);
    for (PMC p: pmcsMap.values()) {
      Value val = p.valueFor(g.all);
      if (val.compareTo(btValue) < 0) {
        btValue = val;
      }
    }
    if (TRACE) {
      System.out.println("btValue " + btValue);
    }
  }

  PMC makePMC(XBitSet separator) {
    PMC p = pmcsMap.get(separator);
    if (p == null) {
      p = new PMC(separator);
      pmcsMap.put(separator, p);
    }
    return p;
  }

  Block makeBlock(XBitSet component)  {
    Block f = blocksMap.get(component);
    if (f == null) {
      f = new Block(component);
      blocksMap.put(component, f);
    }
    return f;
  }

  Block makeBlock(XBitSet component, XBitSet separator) {
    Block f = blocksMap.get(component);
    if (f == null) {
      f = new Block(component, separator);
      blocksMap.put(component, f);
    }
    return f;
  }

  class Block implements Comparable<Block> {
    XBitSet component;
    XBitSet separator;
//    XBitSet outbound;
    boolean queued;
    boolean processed;
    PMC cap;
    Set<PMC> caps;
    Value value;

    Block(XBitSet component) {
      this(component, g.neighborSet(component));
    }

    Block(XBitSet component, XBitSet separator) {
      this.component = component;
      this.separator = separator;
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      assert component.equals(g.all) || fulls.size() >= 2;
//      outbound = null;
//      for (XBitSet full: fulls) {
//        if (outbound == null || full.nextSetBit(0) < outbound.nextSetBit(0)) {
//          outbound = full;
//        }
//      }
//      assert component.equals(g.all) || !outbound.equals(component); 
    }

    boolean subsumesSome(Set<Block> iBlocks) {
      for (Block ib: iBlocks) {
        if (ib.component.isSubset(component)) {
          return true;
        }
      }
      return false;
    }

    void evaluate() {
      int w = weightOf(component.unionWith(separator));
      value = new Value(w, 1);
      if (caps != null) {
        for (PMC cap: caps) {
          Value val = cap.valueFor(component);
          if (val.compareTo(value) < 0) {
            value = val;
          }
        }
      }
    }
    
 
    void addCap(PMC cap) {
      if (caps == null) {
        caps = new HashSet<>();
      }
      caps.add(cap);
    }

//    void queue() {
//      if (queued) {
//        return;
//      }
//      queued = true;
//      queue.add(this);
//    }

    int fillTD(TreeDecomposition td) {
      if (caps == null) {
        return td.addBag(separator.unionWith(component).toArray());
      }
      
      PMC cap = bestCap();
      int b = td.addBag(cap.separator.toArray());
      for (Block f: cap.subblocks) {
        if (f.component.isSubset(component)) {
          int b1 = f.fillTD(td);
          td.addEdge(b,  b1);
        }
      }
      return b;
    }


    PMC bestCap() {
      assert caps != null: this;
      PMC best = null;
      for (PMC cap: caps) {
        if (best == null ||
            cap.valueFor(component).compareTo(best.valueFor(component)) < 0) {
          best = cap;
        }
      }
      return best;
    }

    @Override 
    public int hashCode() {
      return component.hashCode();
    }

    @Override 
    public boolean equals(Object x) {
      Block f = (Block) x;
      return component.equals(f.component);
    }

    @Override
    public int compareTo(Block f) {
      return XBitSet.cardinalityComparator.compare(component, f.component);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("iBlock: separator " + separator + " vertices " + component + " value " + value);
      if (caps != null) {
        sb.append(" " + caps.size() + " caps");
      }
      else {
        sb.append(" caps null");
      }
      return sb.toString();
    }
  }

  class PMC {
    XBitSet separator;
    Block[] subblocks;
    Block toCap;
    int weight;

    PMC(XBitSet separator) {
      this.separator = separator;
      assert g.isPMC(separator);
      ArrayList<XBitSet> components = g.separatedComponents(separator);
      components.sort(XBitSet.cardinalityComparator);

      Set<XBitSet> minSeps = new HashSet<>();
      subblocks = new Block[components.size()];
      for (int i = 0; i < components.size(); i++) {
        subblocks[i] = makeBlock(components.get(i));
        minSeps.add(subblocks[i].separator);
      }

      for (XBitSet sep: minSeps) {
        toCap = innerBlock(sep);
        toCap.addCap(this);  
      }
      
      weight = weightOf(separator);
    }

    TreeDecomposition getUncontractedTD() {
      TreeDecomposition td = new TreeDecomposition(0, 0, g);
      int r = td.addBag(separator.toArray());
      for (Block block: subblocks) {
        int b = block.fillTD(td);
        td.addEdge(r, b);
      }
      return td;
    }

    Block innerBlock(XBitSet sep) {
      XBitSet remSep = separator.subtract(sep);
      assert !remSep.isEmpty();
      XBitSet union = (XBitSet) remSep.clone();
      for (Block b: subblocks) {
        if (b.separator.intersects(remSep)) {
          union.or(b.component);
        }
      }
      return makeBlock(union);
    }

    Value valueFor(XBitSet component) {
      Value val = new Value(weight, 1);
      for (Block ib: subblocks) {
        if (ib.component.isSubset(component)) {
          val.add(ib.value);
        }
      }
      return val;
    }

    @Override
    public String toString() {
      return "pmc " + separator + " " + subblocks.length + " subblocks";
    }
    
    @Override
    public int hashCode() {
      return separator.hashCode();
    }
    
    @Override
    public boolean equals(Object x) {
      PMC p = (PMC) x;
      return separator.equals(p.separator);
    }
  }

  int weightOf(XBitSet vs) {
    XBitSet vs1 = vs.convert(minor.map);
    return vs1.cardinality() - 1;
//    int w = 2 * (vs1.cardinality() - 1);
//    if (!h.isPMC(vs1)) {
//      w--;
//    }
//    return w; 
  }
}
