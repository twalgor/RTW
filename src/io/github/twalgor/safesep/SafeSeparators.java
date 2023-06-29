package io.github.twalgor.safesep;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;

public class SafeSeparators {
//  static final boolean TRACE = true;
  static final boolean TRACE = false;
  static final int EXACT_SAFE_SEP_MAX = 20;
  static final String VERSION = "2";

  Graph g;
  TreeDecomposition td;
  int k;
  Graph treeOfTD;
  
  public SafeSeparators(Graph g, TreeDecomposition td, int k) {
    this.g = g;
    this.td = td;
    this.k = k;
    treeOfTD = td.toTree();
    
  }
  
  public MSC findASafeSep() {
    XBitSet nodes = XBitSet.all(td.nb + 1).removeBit(0);
    XBitSet tightNodes = new XBitSet();
    for (int b: nodes.toArray()) {
      if (td.bags[b].length >= k) {
        tightNodes.set(b);
      }
    }
    for (int b: nodes.toArray()) {
      ArrayList<XBitSet> components = treeOfTD.componentsOf(nodes.removeBit(b));
      for (XBitSet compo: components) {
        if (!compo.intersects(tightNodes)) {
          MSC msc = new MSC(compo, b);
          if (TRACE) {
            System.out.println("msc for " + b + ": " + msc);
          }


          msc.findRCMContraction();
          if (msc.contractions != null) {
            return msc;
          }
        }
      }
    }
    return null;
  }
  
  public class MSC {
    XBitSet treeCompo;
    int anchor;
    public XBitSet component;
    public XBitSet separator;
    Subgraph sub;
    Graph h;
    public Edge[] contractions;
    
    MSC (XBitSet treeCompo, int anchor) {
      this.treeCompo = treeCompo;
      this.anchor = anchor;
      component = td.unionBags(treeCompo)
          .subtract(td.bagAt(anchor));
      separator = g.neighborSet(component);
      assert separator.isSubset(td.bagAt(anchor));
      sub = new Subgraph(g, component.unionWith(separator));
      h = sub.h;
    }
      
    void findRCMContraction() {
      RootedMinorGreedy rmg = new RootedMinorGreedy(h, separator.convert(sub.conv));
      Minor minor0 = rmg.contract();
      Graph f = minor0.getGraph();
      if (f.isClique(f.all)) {
        Minor minor = new Minor(g);
        ArrayList<Edge> availables = new ArrayList<>();
        for (Edge e: g.edgeList()) {
          if (component.get(e.u) && separator.get(e.v) ||
              separator.get(e.u) && component.get(e.v) ||
              component.get(e.u) && component.get(e.v)) {
            int u = sub.conv[e.u];
            int v = sub.conv[e.v];
            if (minor0.map[u] == minor0.map[v]) {
              assert !(separator.get(e.u) && separator.get(e.v));
              availables.add(e);
            }
          }
        }
        ArrayList<Edge> contList = new ArrayList<>();
        while (!component.convert(minor.map).isSubset(separator.convert(minor.map))) {
          assert !availables.isEmpty();
          Edge[] ea = new Edge[availables.size()];
          availables.toArray(ea);
          for (Edge e: ea) {
            availables.remove(e);
            int u = minor.map[e.u];
            int v = minor.map[e.v];
            if (u == v) {
              continue;
            }
            minor = minor.contract(u, v);
            contList.add(e);
            break;
          }
        }
        
        Edge[] ca = new Edge[contList.size()];
        contractions = contList.toArray(ca);
      }
    }

    TreeDecomposition localTD() {
      TreeDecomposition ltd = new TreeDecomposition(0, 0, h);
      int r = ltd.addBag(separator.convert(sub.conv).toArray());
      int rootNode = treeOfTD.neighborSet[anchor].intersectWith(treeCompo).nextSetBit(0);
      int b = fillTD(rootNode, anchor, ltd);
      ltd.addEdge(r,  b);
      return ltd;
    }
    
    int fillTD(int node, int parent, TreeDecomposition ltd) {
      int b = ltd.addBag(new XBitSet(td.bags[node]).convert(sub.conv).toArray());
      XBitSet nb = treeOfTD.neighborSet[node];
      for (int node1 = nb.nextSetBit(0); node1 >= 0; node1 = nb.nextSetBit(node1 + 1)) {
        if (node1 != parent) {
          int b1 = fillTD(node1, node, ltd);
          ltd.addEdge(b, b1);
        }
      }
      return b;
    }
    
    public Set<XBitSet> pmcsForComponent() {
      Set<XBitSet> pmcs = new HashSet<>();
      for (int b: treeCompo.toArray()) {
        pmcs.add(new XBitSet(td.bags[b]));
      }
      return pmcs;
    }
    
    @Override 
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("MSC almost clique? " + 
          g.isAlmostClique(separator) + " separator " + separator +  
          " anchor " + anchor + " treeCopmo " + treeCompo + 
          " missings " + nMissings() + " component " + component);
      return sb.toString();
    }

    private int nMissings() {
      int k = separator.cardinality();
      Subgraph sub = new Subgraph(g, separator);
      return k * (k - 1) / 2 - sub.h.numberOfEdges();
    }
  }
}
