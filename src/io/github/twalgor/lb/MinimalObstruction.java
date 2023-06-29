package io.github.twalgor.lb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import io.github.twalgor.acsd.ACSDecomposition;
import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.decomposer.SemiPID;

public class MinimalObstruction {
  static final String VERSION = "1";
  static boolean TRACE = false;
//  static boolean TRACE = true;
  Graph g;
  int k;
  
  public MinimalObstruction(Graph g, int k) {
    this.g = g;
    this.k = k;
    assert !isFeasible(g, k); // tw(g) is k + 1 or larger
  }
  
  public Minor minimal() {
    ArrayList<Edge> available = g.edgeList();
    sortAvailable(available, g);

    Minor minor = new Minor(g);
    Graph h = g;
    boolean moving = true;
    while (moving) {
      assert !isFeasible(h, k);
      if (TRACE) {
        System.out.println("h.n " + h.n);
      }
      if (h.isClique(h.all)) {
        break;
      }
      moving = false;
      ACSDecomposition acsd = new ACSDecomposition(h);
      acsd.decomposeByACS();
      if (acsd.acAtoms.size() > 1) {
        if (TRACE) {
          System.out.println("acsd of " + acsd.acAtoms.size() + " atoms for h.n " + h.n);
        }
        XBitSet[] aa = acsd.acAtoms.toArray(new XBitSet[acsd.acAtoms.size()]);
        Arrays.sort(aa, (a1, a2) -> - XBitSet.cardinalityComparator.compare(a1,  a2));
        LocalGraph lg = null;
        for (XBitSet atom: aa) {
          LocalGraph lg1 = new LocalGraph(h, atom);
          if (!isFeasible(lg1.h, k)) {
            lg = lg1;
            break;
          }
        }
        assert lg != null;
        XBitSet[] components = new XBitSet[lg.h.n];
        for (int v = 0; v < components.length; v++) {
          components[v] = new XBitSet(new int[] {lg.inv[v]});
        }
        ArrayList<XBitSet> compos = h.separatedComponents(lg.h.all.convert(lg.inv));
        for (XBitSet compo: compos) {
          XBitSet sep = h.neighborSet(compo);
          int w = extraVertex(sep, h);
          assert w >= 0;
          int v = lg.conv[w];
          components[v].or(compo);
        }
        Minor minor1 = new Minor(h, components);
        minor = minor1.composeWith(minor);
        if (TRACE) {
          System.out.println(h.n + " -> " + minor.m + " by ACSD");
        }
        h = minor.getGraph();
        moving = true;
        assert !isFeasible(h, k);
        available = inheritAvailable(available, minor1, null);
        continue;
      }
      Set<Edge> rejected = new HashSet<>();
      for (Edge e: available.toArray(new Edge[available.size()])) {
        available.remove(e);
        Minor minor1 = minor.contract(e.u, e.v);
        Graph h1 = minor1.getGraph();
        if (!isFeasible(h1, k)) {
          if (TRACE) {
            System.out.println("e: " + e);
          }
          Minor iMinor = minor1.rebase(minor);
          available = inheritAvailable(available, iMinor, rejected);
          minor = minor1;
          h = h1;
          moving = true;
          break;
        }
        else {
          rejected.add(e);
        }
      }
    }
    return minor;
  }

  ArrayList<Edge> inheritAvailable(ArrayList<Edge> available, Minor minor, Set<Edge> rejected) {
    Graph h = minor.getGraph();
    ArrayList<Edge> inherited = new ArrayList<>();
    for (Edge e: available) {
      int u = minor.map[e.u];
      int v = minor.map[e.v];
      if (u != v) {
        inherited.add(new Edge(u, v, h.n));
      }
    }
    if (rejected != null) {
      Set<Edge> rejected1 = new HashSet<>();
      for (Edge e: rejected) {
        int u = minor.map[e.u];
        int v = minor.map[e.v];
        assert u != v;
        rejected1.add(new Edge(u, v, h.n));
      }
      inherited.removeAll(rejected1);
    }
    sortAvailable(inherited, h);
    return inherited;
  }

  int extraVertex(XBitSet sep, Graph h) {
    for (int v: sep.toArray()) {
      if (h.isClique(sep.removeBit(v))) {
        return v;
      }
    }
    return -1;
  }

  boolean isFeasible(Graph h, int k) {
    SemiPID spid = new SemiPID(h, k, false);
    return spid.isFeasible();
  }

  void sortAvailable(ArrayList<Edge> available, Graph h){
    Map<Edge, Integer> valueMap = new HashMap<>();
    for (Edge e: available) {
      valueMap.put(e, evaluate(e, h));
    }
    available.sort((e1, e2) -> valueMap.get(e1) - valueMap.get(e2));
  }

  int evaluate(Edge e, Graph h) {
    int u = e.u;
    int v = e.v;

    return Math.min(deff(u, v, h), deff(v, u, h));
  }

  int deff(int u, int v, Graph h) {
    XBitSet nb = h.neighborSet[u].removeBit(v);
    int missing = 0;
    for (int w = nb.nextSetBit(0); w >= 0; w = nb.nextSetBit(w + 1)) {
      XBitSet miss = nb.subtract(h.neighborSet[w]).removeBit(w);
      missing += miss.cardinality();
    }
    return missing / 2;
  }

}
