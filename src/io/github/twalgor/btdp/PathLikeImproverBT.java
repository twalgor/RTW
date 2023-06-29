package io.github.twalgor.btdp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import io.github.twalgor.btdp.BTDP.Block;
import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;

public class PathLikeImproverBT {
  
  Graph g;
  int budget;
  public Set<XBitSet> pmcs;
  BTDP btdp;
  public Value value;
  public int nTick;

  Set<XBitSet> searched;
  Set<XBitSet> newPMCs;
  
  

  public PathLikeImproverBT(Graph g, Set<XBitSet> pmcs) {
    this.g = g;
    this.pmcs = pmcs;
    btdp = new BTDP(g, pmcs);
    btdp.doDP();
    btdp.filter();
    pmcs = btdp.pmcs;
    value = btdp.value;
  }
  
  public void importPMCs(Set<XBitSet> pmcs) {
    this.pmcs.addAll(pmcs);
    btdp = new BTDP(g, pmcs);
    btdp.doDP();
    btdp.filter();
    pmcs = btdp.pmcs;
    value = btdp.value;
  }
  
  public void improve(int budget) {
    this.budget = budget;
    nTick = 0;
    searched = new HashSet<>();
    while (nTick < budget) {
      XBitSet f = laregestFeasible();
      if (f == null) {
        break;
      }
      searched.add(f);
      newPMCs = new HashSet<>();
      search(f);
      btdp.importPMCs(newPMCs);
      btdp.doDP();
      if (btdp.value.compareTo(value) < 0) {
        value = btdp.value;
        btdp.filter();
        pmcs = btdp.pmcs;
        return;
      }
    }
  }
  
  public void prune(int maxPMCs) {
    btdp.prune(maxPMCs);
    assert btdp.value.equals(value);
    pmcs = btdp.pmcs;
  }
  
  XBitSet laregestFeasible() {
    XBitSet largest = null;
    for (Block block: btdp.blockMap.values()) {
      if (block.value.compareTo(value) < 0 &&
          !searched.contains(block.component)) {
        if (largest == null || 
            block.component.cardinality() > largest.cardinality()) {
          largest = block.component;
        }
      }
    }
    return largest;
  }

  TreeDecomposition greedyDecomposition(Graph h) {
    nTick += h.n;
    Graph t = h.copy();
    MMAF mmaf = new MMAF(t);
    mmaf.triangulate();
    TreeDecomposition td = Chordal.chordalToTD(t);
    td.g = h;
    return td;
  }

  public TreeDecomposition getTD() {
    return btdp.aDecomposition();
  }
  
  String indent(XBitSet component) {
    int n = g.n - component.cardinality();
    return n + ":" + spaces(n % 50);
  }

  String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  void search(XBitSet component) {
    XBitSet sep = g.neighborSet(component);
    assert g.fullComponents(sep).size() >= 2;
    for (int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
      if (nTick > budget) {
        return;
      }
      nTick++;
      XBitSet bag = sep.unionWith(g.neighborSet[v].subtract(component));
      assert g.isWellSeparating(bag);

      if (bag.cardinality() > value.width) {
        continue;
      }

      XBitSet closure = bag.unionWith(component);

      ArrayList<XBitSet> components = g.separatedComponents(closure);
      if (hasLargeMinimalSeprator(components)) {
        continue;
      }

      LocalGraph lg = new LocalGraph(g, bag);
      TreeDecomposition td = greedyDecomposition(lg.h);
      if (td.width >= btdp.value.width) {
        continue;
      }
      Set<XBitSet> pmcs1 = XBitSet.convertAll(td.setOfBags(), lg.inv);
      newPMCs.addAll(pmcs1);

      for (XBitSet compo: components) {
        Block b = btdp.blockMap.get(compo);
        if (b != null && b.value.width < value.width) {
          continue;
        }
        XBitSet sep1 = g.neighborSet(compo);
        Subgraph sub = new Subgraph(g, compo.unionWith(sep1));
        sub.h.fill(sep1.convert(sub.conv));
        TreeDecomposition td1 = greedyDecomposition(sub.h);
        //            System.out.println(indent(component) + "width " + td1.width + " for " + compo);
        if (td1.width < value.width) {
          Set<XBitSet> pmcs2 = XBitSet.convertAll(td1.setOfBags(), sub.inv); 
          newPMCs.addAll(pmcs2);
        }
      }
    }
  }

  XBitSet internalComponent(XBitSet outer, XBitSet bag) {
    XBitSet sep = g.neighborSet(outer);
    assert sep.isSubset(bag);
    ArrayList<XBitSet> fulls = g.fullComponents(sep);
    assert fulls.size() >= 2;
    for (XBitSet full: fulls) {
      if (full.intersects(bag)) {
        return full;
      }
    }
    assert false;
    return null;
  }

  boolean hasLargeMinimalSeprator(ArrayList<XBitSet> components) {
    for (XBitSet compo: components) {
      XBitSet sep = g.neighborSet(compo);
      if (sep.cardinality() >= value.width) {
        return true;
      }
    }
    return false;
  }
}
