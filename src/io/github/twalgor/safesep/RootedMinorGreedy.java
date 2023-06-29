package io.github.twalgor.safesep;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;

public class RootedMinorGreedy {
//  static boolean TRACE = true;
  static boolean TRACE = false;

  Graph g;
  XBitSet root;
  int nr;
  
  public RootedMinorGreedy (Graph g, XBitSet root) {
    this.g = g;
    this.root = root;
    nr = root.cardinality();
    if (TRACE) {
      System.out.println("RootedMinorGreedy n " + g.n + " root " + root);
    }
  }
  
  public Minor contract() {
    Minor minor = new Minor(g);
    while (minor.m > nr) {
      if (TRACE) {
        System.out.println("minor.m " + minor.m + " nr " + nr);
      }
      Graph h = minor.getGraph();
      XBitSet root1 = root.convert(minor.map);
      Minor best = null;
      int maxMinBest = 0;
      for (int v = root1.nextSetBit(0); v >= 0; v = root1.nextSetBit(v + 1)) {
        XBitSet nb = h.neighborSet[v].subtract(root1);
        for (int w = nb.nextSetBit(0); w >= 0; w = nb.nextSetBit(w + 1)) {
          Minor minor1 = minor.contract(v, w);
          int mm = minDeg(minor1.getGraph(), root.convert(minor1.map));
          if (best == null || mm > maxMinBest) {
            best = minor1;
            maxMinBest = mm;
          }
        }
      }
      minor = best;
    }
    return minor;
  }

  int minDeg(Graph h, XBitSet vs) {
    int min = -1;
    for (int v = vs.nextSetBit(0); v >= 0; v = vs.nextSetBit(v + 1)) {
      int deg = h.neighborSet[v].cardinality();
      if (min == -1 || deg < min) {
        min = deg;
      }
    }
    return min;
  }
 
}