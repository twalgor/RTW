package io.github.twalgor.decomposer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.MinimalizeTD;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.minseps.MinSepsGenerator;

public class SemiExact {
  Graph g;
  int k;
  int nMinSeps;
  public Set<XBitSet> minSeps;
  SemiPID spid;
  public boolean isExact;
  
  public SemiExact(Graph g, int k, Set<XBitSet> minSeps, int nMinSeps) {
    assert g.isConnected(g.all);
    this.g = g;
    this.k = k;
    if (minSeps == null) {
      this.minSeps = basicMinSeps();
    }
    else {
      this.minSeps = new HashSet<>();
      for (XBitSet sep: minSeps) {
        if (sep.cardinality() <= k) {
          this.minSeps.add(sep);
        }
      }
    }
    this.nMinSeps = nMinSeps;
    assert g.isConnected(g.all);
  }
  
  Set<XBitSet> basicMinSeps() {
    Set<XBitSet> minSeps = new HashSet<>();
    for (int v = 0; v < g.n; v++) {
      XBitSet closure = g.neighborSet[v].addBit(v);
      ArrayList<XBitSet> components = g.separatedComponents(closure);
      for (XBitSet compo: components) {
        XBitSet sep = g.neighborSet(compo);
        if (sep.cardinality() <= k) {
          minSeps.add(sep);
        }
      }
    }
    return minSeps;
  }

  public boolean isFeasible() {
    expandMinSeps();
//    System.out.println(minSeps.size() + " minSeps");
    if (minSeps.size() < nMinSeps) {
      MinSepsGenerator msg = new MinSepsGenerator(g, k);
      msg.generate();
      minSeps = msg.minSeps;
      isExact = true;
    }
    for (XBitSet sep: minSeps) {
      assert sep.cardinality() <= k;
    }
    spid = new SemiPID(g, k, minSeps, false);
    return spid.isFeasible();
  }
  
  void expandMinSeps() {
    int n = minSeps.size();
    while (n < nMinSeps) {
      XBitSet[] msa = minSeps.toArray(new XBitSet[minSeps.size()]);
      for (XBitSet minSep: msa) {
        expand(minSep);
      }
      if (minSeps.size() == n) {
        return;
      }
      n = minSeps.size();
    }
    return;
  }
  
  void expand(XBitSet minSep) {
    ArrayList<XBitSet> components = g.separatedComponents(minSep);
    for (XBitSet compo: components) {
      for (int v: minSep.toArray()) {
        XBitSet compo1 = compo.addBit(v);
        XBitSet nb = g.neighborSet(compo1);
        ArrayList<XBitSet> compos = g.separatedComponents(nb.unionWith(compo1));
        for (XBitSet c: compos) {
          XBitSet sep = g.neighborSet(c);
          if (sep.cardinality() <= k) {
            minSeps.add(sep);
            if (minSeps.size() >= nMinSeps) {
              return;
            }
          }
        }
      }
    }
  }

  public TreeDecomposition getTD() {
    return spid.decompose();
  }

  public Set<XBitSet> generateConducives() {
    Set<XBitSet> conducives = new HashSet<>();
  
    boolean moving = true;
    while (moving && conducives.size() < g.n * 2) {
      moving = false;
      int nc = conducives.size();
      SemiPID spid = new SemiPID(g, k, minSeps, false);
      TreeDecomposition td = spid.decompose();
      if (td == null) {
        return conducives;
      }
      td = MinimalizeTD.minimalize(td);
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
    for (XBitSet sep: td.setOfSeparators()) {
      int lc = largestCompoSize(sep, td.g);
      if (best == null || 
          lc < lcBest) {
        lcBest = lc;
        best = sep;
      }
    }
    return best;
  }

  int largestCompoSize(XBitSet sep, Graph g) {
    ArrayList<XBitSet> components = g.separatedComponents(sep);
    return XBitSet.largest(components).cardinality();
  }

  
  
}
