package io.github.twalgor.lb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.Stack;

import io.github.twalgor.acsd.ACSDecomposition;
import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.decomposer.SemiPID;
import io.github.twalgor.log.Log;
import io.github.twalgor.minseps.MinSepsGenerator;

public class NaiveContractionLB {
//  static final boolean TRACE = true;
static final boolean TRACE = false;
  static final String VERSION = "1";
  public static final int BUDGET_LB = 1000;

  Graph g;
  Edge[] allEdges;
  public int lb;
  public Minor obs;
  public boolean exact;
  
  Random random;
  
  static Log log;
  static long t0;

  public NaiveContractionLB(Graph g) {
    this.g = g;
    if (t0 == 0) {
      t0 = System.currentTimeMillis();
    }
    allEdges = g.edgeArray();
  }
  
  public void lowerBound() {
    Set<Edge> availables = new HashSet<>(g.edgeList());
    Minor[] minor = new Minor[g.n + 1];
    minor[g.n] = new Minor(g);
    Graph h = g;
    int n = g.n;
    while (n > h.minDegree() * 2) {
      Edge e = bestCont(availables, minor[n]);
      minor[n - 1] = minor[n].contract(minor[n].map[e.u], minor[n].map[e.v]);
      availables = filterEdges(availables, minor[n - 1]);
      h = minor[n - 1].getGraph();
      n--;
    }

    lb = widthOf(h);
    
    if (TRACE) {
      System.out.println("initial lb " + lb + " minor.m " + n);
    }
    
    while (n < g.n) {
      n++;
      h = minor[n].getGraph();
      Set<XBitSet> minSeps = minSeps(h, lb);
      if (minSeps.size() > BUDGET_LB) {
        break;
      }
      while (!isFeasible(h, lb, minSeps)) {
        lb++;
        if (TRACE) {
          System.out.println("raised lb " + lb + " minor.m " + n);
        }
        minSeps = minSeps(h, lb);
        if (minSeps.size() > BUDGET_LB) {
          break;
        }
      }
    }
    MinimalObstruction mo = new MinimalObstruction(h, lb -1);
    obs = mo.minimal().composeWith(minor[n]);
  }
 
  Set<XBitSet> minSeps(Graph h, int k) {
    MinSepsGenerator msg = new MinSepsGenerator(h, k);
    msg.generate();
    return msg.minSeps;
  }


  int bestCont(Minor minor, XBitSet candidates) {
    Graph h = minor.getGraph();
    int iBest = -1;
    EdgeValue valueBest = null;
    for (int i: candidates.toArray()) {
      Edge e = allEdges[i];
      Edge f = convertEdge(e, minor);
      EdgeValue ev = new EdgeValue(f, h);
      ev.evaluate();
      if (valueBest == null ||
          ev.compareTo(valueBest) < 0) {
        iBest = i;
        valueBest = ev;
      }
    }
    return iBest;
  }
  
  Edge bestCont(Set<Edge> availables, Minor minor) {
    Graph h = minor.getGraph();
    Edge best = null;
    EdgeValue valueBest = null;
    for (Edge e: availables) {
      Edge f = convertEdge(e, minor);
      EdgeValue ev = new EdgeValue(f, h);
      ev.evaluate();
      if (valueBest == null ||
          ev.compareTo(valueBest) < 0) {
        best = e;
        valueBest = ev;
      }
    }
    return best;
  }

  Set<Edge> filterEdges(Set<Edge> edges, Minor minor) {
    Set<Edge> result = new HashSet<>();
    for (Edge e: edges) {
      if (minor.map[e.u] != minor.map[e.v]) {
        result.add(e);
      }
    }
    return result;
  }
  
  Edge convertEdge(Edge e, Minor minor) {
    return new Edge(minor.map[e.u], minor.map[e.v], minor.m);
  }


  class EdgeValue implements Comparable<EdgeValue>{
    Edge edge;
    Graph h;
    int nMiss1;
    int deg1;
    int nMiss2;
    int deg2;
    
    EdgeValue(Edge edge, Graph h) {
      this.edge = edge;
      this.h = h;
    }
    
    void evaluate() {
      int du = h.neighborSet[edge.u].cardinality();
      int dv = h.neighborSet[edge.v].cardinality();
      int mu = nMissings(edge.u, edge.v, h);
      int mv = nMissings(edge.v, edge.u, h);
      if (compare(mu, du, mv, dv) < 0) {
        deg1 = du;
        nMiss1 = mu;
        deg2 = dv;
        nMiss2 = mv;
      }
      else {
        deg1 = dv;
        nMiss1 = mv;
        deg2 = du;
        nMiss2 = mu;
      }
    }
    
    @Override 
    public int compareTo(EdgeValue ev) {
      int c = compare(nMiss1, deg1, ev.nMiss1, ev.deg1);
      if (c != 0) {
        return c;
      }
      else {
        return compare(nMiss2, deg2, ev.nMiss2, ev.deg2);
      }
    }
    
    int compare(int nMiss1, int deg1, int nMiss2, int deg2) {
      if (nMiss1 * deg2 == nMiss2 * deg1) {
        return deg1 - deg2;
      }
      else {
        return nMiss1 * deg2 - nMiss2 * deg1; 
      }
    }
    
    int nMissings(int u, int v, Graph h) {
      int count = 0;
      XBitSet nb = h.neighborSet[u].removeBit(v);
      for (int w = nb.nextSetBit(0); w >= 0; w = nb.nextSetBit(w + 1)) {
        count += nb.subtract(h.neighborSet[w]).cardinality()  - 1;
      }
      assert count % 2 == 0;
      return count / 2;
    }

  }

  static boolean isFeasible(Graph h, int k) {
    if (h.n <= k + 1) {
      return true;
    }
    SemiPID spid = new SemiPID(h, k, false);
    boolean isFeasible = spid.isFeasible();
    return isFeasible;
  }
  
  static boolean isFeasible(Graph h, int k, Set<XBitSet> minSeps) {
    SemiPID spid = new SemiPID(h, k, minSeps, false);
    boolean isFeasible = spid.isFeasible();
    return isFeasible;
  }
  
  static int widthOf(Graph h) {
    return SemiPID.decompose(h).width;
  }
  
  static SemiPID firstFeasibleSemiPID(Graph h) {
    int k = h.minDegree();
    SemiPID spid = new SemiPID(h, k, false);
    while (!spid.isFeasible()) {
      k++;
      spid = new SemiPID(h, k, false);
    }
    return spid;
  }
  
  static int log2(int n) {
    int count = 0;
    while (n > 0) {
      count++;
      n /= 2;
    }
    return count;
  }
  
  static String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }
  
  public static void main(String args[]) {
    if (args.length == 3) {
      test(args[0], args[1], Integer.parseInt(args[2]));
      return;
    }
    String[] instances = {
//            "Sz512_15127_1.smt2-stp212.gaifman_3",
//            "MD5-32-1.gaifman_4", 
//            "Promedas_69_9", 
//            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_12", 
//            "Promedas_56_8", 
//            "Promedas_48_5", 
//            "minxor128.gaifman_2", 
//            "Promedas_49_8", 
//            "FLA_14", 
//            "post-cbmc-aes-d-r2.gaifman_10", 
//            "Pedigree_11_7", 
//            "countbitsarray04_32.gaifman_10", 
//            "mrpp_4x4#8_8.gaifman_3", 
//            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_9", 
//            "Promedus_38_15", 
//            "Promedas_50_7", 
//        "Promedus_34_11", 
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_15", 
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_14", 
            "Promedas_43_13", 
            "Promedas_46_8", 
            "Promedus_14_9", 
            "jgiraldezlevy.2200.9086.08.40.41.gaifman_2", 
            "modgen-n200-m90860q08c40-14808.gaifman_2", 
            "Promedus_38_14", 
            "Pedigree_11_6", 
            "Promedas_27_8",
            "Promedas_45_7",
            "jgiraldezlevy.2200.9086.08.40.46.gaifman_2",
            "jgiraldezlevy.2200.9086.08.40.22.gaifman_2", 
            "Promedas_25_8", 
            "Pedigree_12_8", 
            "Promedus_34_12", 
            "Promedas_22_6", 
            "aes_24_4_keyfind_5.gaifman_3", 
            "Promedus_18_8", 
            "6s151.gaifman_3", 
            "LKS_15", 
            "Promedas_23_6", 
            "Promedus_28_14", 
            "Promedas_21_9", 
            "Promedas_59_10", 
            "Promedas_60_11", 
            "Promedas_69_10", 
            "newton.3.3.i.smt2-stp212.gaifman_2", 
            "jgiraldezlevy.2200.9086.08.40.167.gaifman_2", 
            "Promedus_34_14", 
            "modgen-n200-m90860q08c40-22556.gaifman_2", 
            "jgiraldezlevy.2200.9086.08.40.93.gaifman_2", 
            "Promedas_61_8",
            "Promedas_30_7", 
            "FLA_13", 
            "am_7_7.shuffled-as.sat03-363.gaifman_6", 
            "LKS_13",
            "SAT_dat.k80-24_1_rule_1.gaifman_3",
            "Promedas_28_10",
            "smtlib-qfbv-aigs-lfsr_004_127_112-tseitin.gaifman_6",
            "Promedas_11_7",
            "Promedus_20_13",
            "Pedigree_13_12",
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_10",
            "Promedas_22_8",
            "FLA_15",
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_15", 
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_13",
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_12", 
            "Promedas_63_8", 
            "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_11", 
            "Pedigree_12_14", 
            "Promedus_12_15", 
            "Promedus_12_14", 
            "Promedas_44_9", 
            "Promedas_32_8", 
            "NY_13", 
            "Promedus_18_10",
            "Promedas_34_8", 
            "Promedas_62_9", 
            "Promedus_17_13", 
            "Promedus_11_15", 
            "Promedas_24_11",
            "Promedus_14_8",
            
            "am_9_9.gaifman_6",
            "NY_11",
            "mrpp_8x8#24_14.gaifman_3",
//            "Promedas_31_8", //*
            "Pedigree_12_10",
            "Promedas_55_9",
//            "aes_24_4_keyfind_5.gaifman_4", //*
            "Pedigree_12_12",
            "Promedas_46_15",
            "Pedigree_13_9",
            "Promedas_51_12",
            "Promedus_27_15",
//            "Promedas_68_13", //*
//            "Promedas_51_14", //*
//            "modgen-n200-m90860q08c40-1585.gaifman_2",//*
//            "Promedas_62_11",//*
//            "Promedas_58_11", //*
//            "Promedas_44_11",//*
//            "atco_enc2_opt2_10_21.gaifman_3" //*
    };

//    for (String inst: instances) {
//      test("../instance/PACE2017bonus_gr/", inst, 0);
//    }

//    test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 0);    

//      test("../instance/he2017secret", "he012", 0);
    
//    test1("../instance/PACE2017bonus_gr/", "atco_enc2_opt2_10_21.gaifman_3", 0, "_bonushard_");
//    test("../instance/PACE2017bonus_gr/", "modgen-n200-m90860q08c40-1585.gaifman_2", 0);
//    test1("../instance/PACE2017bonus_gr/", "Promedas_62_11", 0, "_bonushard_");
//    test1("../instance/PACE2017bonus_gr/", "Promedas_48_11", 0, "_bonushard_");
//    test1("../instance/PACE2017bonus_gr/", "Promedas_44_11", 0, "_bonushard_");
//  test1("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0, "_retry_");
//    test("../instance/PACE2017bonus_gr/", "mrpp_4x4#8_8.gaifman_3", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_14", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_34_11", 0);
//    test("../instance/PACE2017bonus_gr/", "countbitsarray04_32.gaifman_10", 0);
//  test("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0);
    test("../instance/PACE2017bonus_gr/", "aes_24_4_keyfind_5.gaifman_4", 0);
//    test("../instance/PACE2017bonus_gr/", "modgen-n200-m90860q08c40-1585.gaifman_2", 0);
//    test("../instance/PACE2017bonus_gr/", "mrpp_8x8#24_14.gaifman_3", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_44_11", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_68_13", 0);
//    test("../instance/PACE2017bonus_gr/", "atco_enc2_opt2_10_21.gaifman_3", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_51_14", 0);
//  test("../instance/PACE2017bonus_gr/", "Promedas_58_11", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_62_11", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_31_8", 0);
//    test1("../instance/PACE2017bonus_gr/", "newton.3.3.i.smt2-stp212.gaifman_2", 0, "_retry_");
//    test("../instance/pace17exact/", "ex039", 0);
  }

  private static void test(String path, String name, int width) {
    test1(path, name, width, "");
  }
  
  private static void test1(String path, String name, int width, String suff) {
    log = new Log("SimpleContractionLB" + suff +
        NaiveContractionLB.VERSION + "_" + 
        NaiveContractionLB.BUDGET_LB, 
        name);

    Graph g = Graph.readGraph(path, name);
    // Graph g = Graph.readGraph("instance/" + path, name);

    log.log("Graph " + name + " read, n = " + g.n + ", m = " + g.numberOfEdges());

    t0 = System.currentTimeMillis();
    ACSDecomposition acsd = new ACSDecomposition(g);
    acsd.decomposeByACS();
    XBitSet largestAtom = null;
    for (XBitSet atom : acsd.acAtoms) {
      if (largestAtom == null || atom.cardinality() > largestAtom.cardinality()) {
        largestAtom = atom;
      }
    }

    log.log("Largest atom: " + largestAtom.cardinality());

    LocalGraph local = new LocalGraph(g, largestAtom);
    
    NaiveContractionLB nclb = new NaiveContractionLB(local.h);
    
    nclb.lowerBound();
    
    log.log(name + " lb " + nclb.lb);
  }
}
