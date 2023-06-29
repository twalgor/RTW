package io.github.twalgor.safesep;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.XBitSet;

public class RootedMinorBoundedDepthBacktrack extends RootedMinor {
  static final int N_MAX = 20;
  public Minor rMinor;
  
  public RootedMinorBoundedDepthBacktrack(Graph g, XBitSet root) {
    super(g, root);
    assert root.isSubset(g.all);
  }
  
  @Override
  public boolean hasCliqueMinor() {
    Subgraph sub = new Subgraph(g, root);
//    System.out.println("hasCliqueMinor n " + g.n + " root " + root +
//        " ne " + sub.h.numberOfEdges() + " almost-clique " + 
//        g.isAlmostClique(root));
    
    for (int v : root.toArray()) {
      if (g.isClique(root.removeBit(v))) {
        XBitSet[] compos = new XBitSet[root.cardinality()];
        int i = 0;
        for (int w : root.toArray()) {
          if (w == v) {
            compos[i] = g.all.subtract(root).addBit(v);
          }
          else {
            compos[i] = new XBitSet(new int[] {w});
          }
          i++;
        }
        rMinor = new Minor(g, compos);
        return true;
      }
    }
    Map<Integer, XBitSet[]> map = initialMap();
    Minor minor = new Minor(g);
//    System.out.println(g.n + " " + g.isConnected(g.all));
//    g.printRaw(System.out);
//    for (int v: map.keySet()) {
//      System.out.println(v + " " + map.get(v)[0] + " " + map.get(v)[1]);
//    }
    searchBestMinor(0, minor, map);

    Graph h = rMinor.getGraph();
    return h.numberOfEdges() == h.n * (h.n - 1) / 2;
  }
  
  void searchBestMinor(int d, Minor minor, Map<Integer, XBitSet[]> map) {
//    System.out.println(d + " " + minor.m + " " + map.size());
    if (map.isEmpty()) {
      if (rMinor == null ||
          deff(minor.getGraph()) < deff(rMinor.getGraph())) {
        rMinor = minor;
      }
      return;
    }
    if (d >= N_MAX) {
      while (minor.m > root.cardinality()) {
        Minor minor1 = bestGreedyContraction(minor);
        if (minor1 == null) {
          minor = restrictMinor(minor, root);
        }
        else {
          minor = minor1;
        }
      }
      if (rMinor == null ||
          deff(minor.getGraph()) < deff(rMinor.getGraph())) {
        rMinor = minor;
      }
      return;
    }
    
    int v = bestVertex(map);
    if (v == -1) {
      return;
    }
    XBitSet[] val = map.get(v);
    XBitSet nb = val[0].intersectWith(val[1]);
    for (int r = nb.nextSetBit(0); r >= 0; r = nb.nextSetBit(r + 1)) {
      Minor minor1 = minor.contract(minor.map[r], minor.map[v]);
      Map<Integer, XBitSet[]> map1 = updateNeighbors(r, v, map);
      searchBestMinor(d + 1, minor1, map1);
      if (rMinor != null &&
          deff(rMinor.getGraph()) == 0) {
        return;
      }
    }

    if (!val[1].isSubset(nb)) {
      Map<Integer, XBitSet[]> map1 = new HashMap<>();
      for (int w: map.keySet()) {
        if (w != v) {
          map1.put(w, map.get(w));
        }
      }
      map1.put(v, new XBitSet[] {val[0], val[1].subtract(nb)});
      searchBestMinor(d, minor, map1);
    }
  }

  Minor restrictMinor(Minor minor, XBitSet root) {
    XBitSet[] components = new XBitSet[root.cardinality()];
    int i = 0;
    for (XBitSet compo: minor.components) {
      if (compo.intersects(root)) {
        components[i++] = compo;
      }
    }
    assert i == root.cardinality();
    return new Minor(minor.g, components);
  }

  Minor bestGreedyContraction(Minor minor) {
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
    assert best != null;
    return best;
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

  Map<Integer, XBitSet[]> updateNeighbors(int r, int v, Map<Integer, XBitSet[]> map) {
    Map<Integer, XBitSet[]> map1 = new HashMap<>();
    for (int w: map.keySet()) {
      if (w == v) {
        continue;
      }
      XBitSet[] val = map.get(w);
      if (!val[0].get(r) && g.neighborSet[v].get(w)) {
        map1.put(w, new XBitSet[] {val[0].addBit(r), val[1]});  
      }
      else {
        map1.put(w, val);
      }
    }
    return map1;
  }

  int bestVertex(Map<Integer, XBitSet[]> map) {
    assert !map.isEmpty();
    int best = -1;
    int tBest = 0;
    for (int v: map.keySet()) {
      XBitSet[] val = map.get(v);
//      System.out.println(v + " " + val[0] + " " + val[1]);
      XBitSet target = val[0].intersectWith(val[1]);
      if (target.isEmpty()) {
        continue;
      }
      if (best == -1 ||
          target.cardinality() < tBest) {
        best = v;
        tBest = target.cardinality();
      }
    }
    return best;
  }

  Map<Integer, XBitSet[]> initialMap() {
    Map<Integer, XBitSet[]> map = new HashMap<>();
    for (int v = 0; v < g.n; v++) {
      if (root.get(v)) {
        continue;
      }
      map.put(v, new XBitSet[] {
          g.neighborSet[v].intersectWith(root),
          root
          });
    }
    return map;
  }

  int deff(Graph h) {
    return h.n * (h.n - 1) / 2 - h.numberOfEdges();
  }

}
