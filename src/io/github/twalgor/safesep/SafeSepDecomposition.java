package io.github.twalgor.safesep;

import java.io.File;
import java.util.ArrayList;
import java.util.Set;

import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.greedy.MMAF;

public class SafeSepDecomposition {
  static final boolean TRACE = false;
//  static final boolean TRACE = true;
  static final int DEFF_BOUND_FOR_BACKTRACK = 2;
  static String resultPath = "safesep_dec/";

  Graph g;
  public Graph h;
  public Set<XBitSet> acAtoms;
  ArrayList<XBitSet> filledSeps;
  int width;
  
  enum Method {acOnly, greedy, greedyAndBacktrack};
  Method method;
  
  public SafeSepDecomposition(Graph g) {
    this(g, Method.greedyAndBacktrack);
  }
  
  public SafeSepDecomposition(Graph g, Method method) {
    this.g = g;
    this.method = method;
  }
  
  public TreeDecomposition decomposeSafe() {
    TreeDecomposition td = greedyDecomposition(g);
    if (TRACE) {
      System.out.println("n " + g.n + " ub " + td.width);
    }
    Graph tree = td.toTree();
    XBitSet nodes = XBitSet.all(td.nb + 1).removeBit(0);

    ArrayList<Edge> safeEdges = new ArrayList<>();
    XBitSet criticals = new XBitSet();
    if (method != Method.acOnly) {
      int lb = lowerbound(g);
      if (TRACE) {
        System.out.println("lb " + lb);
      }
      for (int b: nodes.toArray()) {
        if (td.bags[b].length >= lb + 1) {
          criticals.set(b);
        }
      }
    }

    if (TRACE) {
      System.out.println("criticals " + criticals);
    }
    Edge[] treeEdges = tree.edgeArray();

//    System.out.println(treeEdges.length + " edges for td.nb " + td.nb);
    for (Edge te: treeEdges) {
      int b1 = te.u;
      int b2 = te.v;
      XBitSet separator = td.bagAt(b1).intersectWith(td.bagAt(b2));
      if (g.isAlmostClique(separator)) {
        if (TRACE) {
          System.out.println("almost clique sep " + separator);
        }
        safeEdges.add(te);
        continue;
      }
      if (method == Method.acOnly) { 
        continue;
      }
      XBitSet subtree1 = subtree(tree, nodes, b1, b2);
      XBitSet subtree2 = subtree(tree, nodes, b2, b1);
      
//      System.out.println(subtree1 + " " + subtree1.intersects(criticals));
//      System.out.println(subtree2 + " " + subtree2.intersects(criticals));
      if (!subtree1.intersects(criticals)) {
        RootedMinorInstance rmi1 = new RootedMinorInstance(b2, td, subtree1);
        if (rmi1.isSafe()) {
          safeEdges.add(te);
        }
      }
      else if (!subtree2.intersects(criticals)) {
        RootedMinorInstance rmi2 = new RootedMinorInstance(b1, td, subtree2);
        if (rmi2.isSafe()) {
          safeEdges.add(te);
        }
      }
//      else {
//        RootedMinorInstance rmi1 = new RootedMinorInstance(b2, td, subtree1);
//        RootedMinorInstance rmi2 = new RootedMinorInstance(b1, td, subtree2);
//        if (rmi1.isSafe() && rmi2.isSafe()) {
//          safeEdges.add(te);
//        }
//      }
    }

//    System.out.println(safeEdges.size() + " safe edges");
    
    Graph forest = tree.copy();
    for (Edge e: safeEdges) {
      forest.removeEdge(e.u, e.v);
    }
    ArrayList<XBitSet> trees = forest.componentsOf(nodes);
    
    TreeDecomposition safeSepDec = new TreeDecomposition(0, 0, g);
    
    int[] map = new int[td.nb + 1];
    for (int i = 0; i < trees.size(); i++) {
      XBitSet t = trees.get(i);
      XBitSet bag = td.unionBags(t);
      int b = safeSepDec.addBag(bag.toArray());
      assert b == i + 1;
      for (int b1: t.toArray()) {
        map[b1] = b;
      }
    }
    
    for (int b = 1; b <= safeSepDec.nb; b++) {
      XBitSet t = trees.get(b - 1);
      for (int b1: t.toArray()) {
        for (int b2: tree.neighborSet[b1].toArray()) {
          int b3 = map[b2];
          if (b3 > b) {
            safeSepDec.addEdge(b, b3);
          }
        }
      }
    }
    return safeSepDec;
  }
  
  XBitSet subtree(Graph tree, XBitSet nodes, int b1, int b2) {
    ArrayList<XBitSet> subtrees = tree.componentsOf(nodes.removeBit(b2));
    for (XBitSet subtree: subtrees) {
      if (subtree.get(b1)) {
        return subtree;
      }
    }
    assert false;
    return null;
  }

  private TreeDecomposition greedyDecomposition(Graph g) {
    Graph t = g.copy();
    MMAF mmaf = new MMAF(t);
    mmaf.triangulate();
    TreeDecomposition td = Chordal.chordalToTD(t);
    td.g = g;
    return td;
  }

  class RootedMinorInstance {
    int b;
    int b0;
    TreeDecomposition td;
    Subgraph sub;

    Graph h;
    XBitSet root;
    TreeDecomposition localTD;
    Minor greedyMinor;
    
    RootedMinorInstance(int b, TreeDecomposition td, XBitSet subtree) {
      this.b = b;
      this.td = td;
      XBitSet component = td.unionBags(subtree).subtract(td.bagAt(b));
      XBitSet separator = g.neighborSet(component);
      XBitSet vs = component.unionWith(separator);
      sub = new Subgraph(g, vs);
      h = sub.h;
      root = separator.convert(sub.conv);
      
      
      Graph tree = td.toTree();
      XBitSet nbb = tree.neighborSet[b].intersectWith(subtree);
      assert nbb.cardinality() == 1;
      b0 = nbb.nextSetBit(0);
      if (TRACE) {
        System.out.println(this);
      }
    }
    
    boolean isSafe() {
      if (h.isAlmostClique(root)) {
        if (TRACE) {
          System.out.println("almostClique " + this);
        }
        return true;
      }
      if (TRACE) {
        System.out.println("not almostClique " + this);
      }
      switch (method) {
      case acOnly:
        return false;
      case greedy:
      case greedyAndBacktrack:
        RootedMinorGreedy rmg = new RootedMinorGreedy(h, root);
        Minor minor = rmg.contract();
        Graph f = minor.getGraph();
        boolean safe = f.numberOfEdges() == f.n * (h.n - 1) / 2;
        if (TRACE) {
          System.out.println("isSafe greedy " + safe + " " + this);
        }
        if (safe || method == Method.greedy) {
          return safe;
        }
        
        if (deff(h) <= DEFF_BOUND_FOR_BACKTRACK) {
          assert root.isSubset(h.all);
          RootedMinorBoundedDepthBacktrack rmbdb =
              new RootedMinorBoundedDepthBacktrack(h, root);
          safe = rmbdb.hasCliqueMinor();
          if (TRACE) {
            System.out.println("isSafe bounded backtrack " + safe + " " + this);
          }
          return safe;
        }
        else {
          return false;
        }
      }
      assert false;
      return false;
    }
    
    int deff(Graph h) {
      return h.n * (h.n - 1) / 2 - h.numberOfEdges();
    }

    @Override
    public String toString() {
      Subgraph sub = new Subgraph(h, root);
      Graph f = sub.h;
      int missings = f.n * (f.n - 1) / 2 - f.numberOfEdges();
      return "RMI b: " + b + " b0 " + b0 +
          " h.n " + h.n + " root " + root + " missings " + missings;
    }
  }

  int lowerbound(Graph f) {
    ContractionLB clb = new ContractionLB(f);
    return clb.lowerbound();
  }

  public static void main(String args[]) {
    //  test1("../instance/PACE2017bonus_gr/", "atco_enc2_opt2_10_21.gaifman_3", 0, "_bonushard_");
    //  test1("../instance/PACE2017bonus_gr/", "modgen-n200-m90860q08c40-1585.gaifman_2", 0, "_bonushard_");
    //  test1("../instance/PACE2017bonus_gr/", "Promedas_62_11", 0, "_bonushard_");
    //  test1("../instance/PACE2017bonus_gr/", "Promedas_48_11", 0, "_bonushard_");
    //  test1("../instance/PACE2017bonus_gr/", "Promedas_44_11", 0, "_bonushard_");
//    test1("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0, "_retry_");
//      test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedas_48_5", 0); 
    //  test("../instance/PACE2017bonus_gr/", "Promedus_38_14", 0); 
    //  test("../instance/PACE2017bonus_gr/", "Promedus_34_11", 0);
    //  test("../instance/PACE2017bonus_gr/", "countbitsarray04_32.gaifman_10", 0);
    test("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0);
//      test("../instance/PACE2017bonus_gr/", "aes_24_4_keyfind_5.gaifman_4", 0);
//      test("../instance/PACE2017bonus_gr/", "modgen-n200-m90860q08c40-1585.gaifman_2", 0);
//      test("../instance/PACE2017bonus_gr/", "Promedas_44_11", 0);
//      test("../instance/PACE2017bonus_gr/", "Promedas_68_13", 0);
//      test("../instance/PACE2017bonus_gr/", "Promedas_51_14", 0);
    //test("../instance/PACE2017bonus_gr/", "Promedas_58_11", 0);
//      test("../instance/PACE2017bonus_gr/", "Promedas_62_11", 0);
    //  test("../instance/PACE2017bonus_gr/", "Promedas_31_8", 0);
    //  test1("../instance/PACE2017bonus_gr/", "newton.3.3.i.smt2-stp212.gaifman_2", 0, "_retry_");

  }

  private static void test(String path, String name, int width) {
    Graph g = Graph.readGraph(path, name);

//    Method method = Method.acOnly;
    Method method = Method.greedy;
//    Method method = Method.greedyLS;
    SafeSepDecomposition ssd = 
        new SafeSepDecomposition(g, method);
    TreeDecomposition td = ssd.decomposeSafe();

    File dir = new File(resultPath + method);
    dir.mkdirs();
    td.save(dir.getPath() + "/" + name + ".td");
  }

}
