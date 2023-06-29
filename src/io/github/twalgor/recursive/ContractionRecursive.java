package io.github.twalgor.recursive;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import io.github.twalgor.acsd.ACSDecomposition;
import io.github.twalgor.btdp.Value;
import io.github.twalgor.common.Chordal;
import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.LocalGraph;
import io.github.twalgor.common.MinimalizeTD;
import io.github.twalgor.common.Minor;
import io.github.twalgor.common.Subgraph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.decomposer.SemiPID;
import io.github.twalgor.greedy.MMAF;
import io.github.twalgor.improver.PIDImprover;
import io.github.twalgor.improver.PIDIterative;
import io.github.twalgor.lb.MinimalObstruction;
import io.github.twalgor.lb.NaiveContractionLB;
import io.github.twalgor.log.Log;
import io.github.twalgor.minseps.MinSepsGenerator;
import io.github.twalgor.safesep.RootedMinorBoundedDepthBacktrack;
import io.github.twalgor.safesep.RootedMinorGreedy;
import io.github.twalgor.safesep.SafeSeparators;
import io.github.twalgor.safesep.SafeSeparators.MSC;
import io.github.twalgor.ulb.SemiPIDConstr;

public class ContractionRecursive {
//  static final boolean TRACE = true;
static final boolean TRACE = false;
//  static final boolean TRACE_DETAIL = true;
  static final boolean TRACE_DETAIL = false;
//  static final boolean STACK_TRACE = true;
static final boolean STACK_TRACE = false;
  static final String VERSION = "11";
  public static final int N_TRY = 1;
  public static final int UNIT_BUDGET_UB = 100;
  public static final int N_CONDUCIVES_RATIO = 10;
  
  Graph g;
  public Minor obs;
  Node root;
  int kTarget;
  int gLB;
  
  Random random;
  
  static Log log;
  static long t0;
    
  public ContractionRecursive(Graph g) {
    this.g = g;
    random = new Random(1);
    
    if (t0 == 0) {
      t0 = System.currentTimeMillis();
    }
  }
  
  public TreeDecomposition decompose() {
    computeWidth();
    return root.aDecomposition();
  }
  
  void computeWidth() {
    NaiveContractionLB nclb = new NaiveContractionLB(g);
    nclb.lowerBound();
    gLB = nclb.lb;
    obs = nclb.obs;
    assert obs != null;
    if (TRACE) {
      System.out.println("initial lower bound " + gLB);
    }

    TreeDecomposition td = greedyDecomposition(g);
    if (TRACE_DETAIL) {
      System.out.println("initial upper bound " + td.width);
    }
    
    PIDImprover pidimp = new PIDImprover(g, td.setOfBags());
    Value val = pidimp.opt;

    if (TRACE) {
      System.out.println("initial value " + val);
    }

    while (true) {
      pidimp.improve(UNIT_BUDGET_UB * 10);
      if (pidimp.opt.compareTo(val) >= 0) {
        break;
      }
      val = pidimp.opt;
      if (TRACE) {
        System.out.println("value improved " + val + " " + 
            pidimp.pmcMap.size() + " pmcs");
      }
    }

    kTarget = val.width - 1;
    PIDIterative pidi = new PIDIterative(g, kTarget);
    pidi.importPMCs(pidimp.pmcs());

    root = new Node(g, pidi);
    
    while (root.ub() > gLB) {
      if (TRACE) {
        System.out.println("target " + kTarget + " lb " + gLB + ", " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      improveUB();
      kTarget = root.ub() - 1;
    }
  }
  
  void improveUB() {
    root.improveUB();   
  }
   
  TreeDecomposition greedyDecomposition(Graph h) {
    Graph h1 = h.copy();
    MMAF mmaf = new MMAF(h1);
    mmaf.triangulate();
    TreeDecomposition td = Chordal.chordalToTD(h1);
    td.g = h;
    return td;
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

  class Node {
    Node parent;
    Edge e;
    Block safeBlock;
    Minor iMinor;
    Minor minor;
    Graph h;
    Node child;
    PIDIterative pidi;

    TreeDecomposition td;

    int ub() {
      if (this == root) {
        return pidi.width();
      }
      if (pidi != null && pidi.width() < root.ub()) {
        return pidi.width();
      }
      else {
        return root.ub();
      }
    }

    int ns;

    ArrayList<Edge> availables;
    Map<Edge, Node> reducerMap;

    int nChild;

    Node(Graph g, PIDIterative pidi) {
      h = g;
      minor = new Minor(g);
      this.pidi = pidi;
      td = pidi.getTD();
      availables = g.edgeList();
      sortAvailables();
      reducerMap = new HashMap<>();
      if (STACK_TRACE) {
        stackTrace();
      }
    }

    Node(Node parent, Edge e) {
      this.parent = parent;
      this.e = e;
      assert parent.h.areAdjacent(e.u, e.v);
      iMinor = new Minor(parent.h);
      iMinor = iMinor.contract(e.u, e.v);
      h = iMinor.getGraph();      
      verifyMinor(iMinor, parent.h, h);
      minor = iMinor.composeWith(parent.minor);
      initialBounds();
      inheritAvailables();
      if (STACK_TRACE) {
        stackTrace();
      }
    }

    Node(Node parent, Edge e, Node ancestor) {
      this.parent = parent;
      this.parent = parent;
      this.e = e;
      assert parent.h.areAdjacent(e.u, e.v);
      iMinor = new Minor(parent.h);
      iMinor = iMinor.contract(e.u, e.v);
      h = iMinor.getGraph();      
      verifyMinor(iMinor, parent.h, h);
      minor = iMinor.composeWith(parent.minor);
      inheritPMCs(ancestor);
    }

    Node(Node parent, Block safeBlock) {
      this.parent = parent;
      this.safeBlock = safeBlock;
      iMinor = new Minor(parent.h);
      for (Edge e: safeBlock.contractions) {
        iMinor = iMinor.contract(iMinor.map[e.u], iMinor.map[e.v]);
      }
      h = iMinor.getGraph();
      verifyMinor(iMinor, parent.h, h);
      minor = iMinor.composeWith(parent.minor);
      initialBounds();
      assert td != null;
      inheritAvailables();
      if (STACK_TRACE) {
        stackTrace();
      }
    }

    void verifyMinor(Minor minor, Graph h1, Graph h2) {
      for (int v = 0;  v < h1.n; v++) {
        int u = minor.map[v];
        assert u >= 0 && u < h2.n;
      }
    }

    void stackTrace() {
      String str = "";
      Node node = this;
      while (node != null) {
        str = digit(node.nChild) + str;
        node = node.parent;
      }
      System.out.println("*" + str + " " + (System.currentTimeMillis() - t0) + " millisecs");
    }
    
    void initialBounds() {
      ns = 1;
      ContractionBT cbt = new ContractionBT(parent.h, iMinor, parent.pidi.pmcs());
      td = cbt.firstTD();
      td = MinimalizeTD.minimalize(td);
      Set<XBitSet> pmcs = td.setOfBags();
      pidi = new PIDIterative(h, kTarget);
      pidi.importPMCs(pmcs);
      if (ub() < root.ub()) {
        if (TRACE) {
          System.out.println(indent() + "inheriting from parent lowered ub");
        }
      }
    }


    void inheritPMCs(Node node) {
      assert node.pidi != null;

      Minor minor1 = minor.rebase(node.minor);
      Set<XBitSet> pmcs1 = node.pidi.pmcs();
      if (pmcs1.size() > h.n * N_CONDUCIVES_RATIO) {
        pmcs1 = node.pidi.conducives(h.n * N_CONDUCIVES_RATIO);
      }
      ContractionBT cbt = new ContractionBT(node.h, minor1, pmcs1);
          
      Set<XBitSet> pmcs = new HashSet<>();
      TreeDecomposition td = cbt.firstTD();
      while (td != null) {
        td = MinimalizeTD.minimalize(td);
        pmcs.addAll(td.setOfBags());
        td = cbt.anotherTD();
      }
      if (pidi == null) {
        pidi = new PIDIterative(h, kTarget);
      }
      pidi.importPMCs(pmcs);
    }

    TreeDecomposition contractTD(TreeDecomposition td, Minor minor) {
      Graph h = minor.getGraph();
      TreeDecomposition td1 = new TreeDecomposition(td.nb, 0, h);
      for (int b = 1; b <= td.nb; b++) {
        td1.bags[b] = td.bagAt(b).convert(minor.map).toArray();
        if (td1.bags[b].length > td1.width + 1) {
          td1.width = td1.bags[b].length - 1;
        }
        td1.degree[b] = td.degree[b];
        td1.neighbor[b] = Arrays.copyOf(td.neighbor[b], td.degree[b]);
      }
      return td1;
    }

    Set<XBitSet> minSepsFrom(XBitSet bag, Graph h) {
      Set<XBitSet> result = new HashSet<>();
      int k = bag.cardinality();
      for (int i = 0; i < (1 << k); i++) {
        if (Integer.bitCount(i) >= k - 5) {
          XBitSet subs = subset(bag, i, k);
          if (h.fullComponents(subs).size() >= 2) {
            result.add(subs);
          }
        }
      }
      return result;
    }

    XBitSet subset(XBitSet bag, int i, int k) {
      int[] ba = bag.toArray();
      XBitSet result = new XBitSet();
      for (int j = 0; j < k; j++) {
        if ((i & (1 << j)) != 0) {
          result.set(ba[j]);
        }
      }
      return result;
    }

    Set<XBitSet> minSepsFrom1(XBitSet bag, Graph h) {
      Set<XBitSet> result = new HashSet<>();
      ArrayList<XBitSet> components = h.separatedComponents(bag);
      for (XBitSet compo: components) {
        XBitSet sep = h.neighborSet(compo);
        if (h.fullComponents(sep).size() >= 2) {
          result.add(sep);
        }
      }
      return result;
    }

    Node bestUBAncestor() {
      assert parent != null;
      Node node = parent;
      int bestUB = parent.ub();
      while (node.parent != null && node.parent.ub() == bestUB) {
        node = node.parent;
      }
      return node;
    }

    Edge[] contractionEdges(Minor minor) {
      Graph g = minor.g;
      Minor minor1 = new Minor(g);
      ArrayList<Edge> ce = new ArrayList<>();
      for (Edge e: g.edgeList()) {
        int u = minor1.map[e.u];
        int v = minor1.map[e.v];
        if (u != v && minor.map[e.u] == minor.map[e.v]) {
          ce.add(e);
          minor1 = minor1.contract(u, v);
        }
      }
      return ce.toArray(new Edge[ce.size()]);
    }

    XBitSet nonSigletonIn(XBitSet[] components) {
      for (XBitSet compo: components) {
        if (compo.cardinality() >= 2) {
          return compo;
        }
      }
      return null;
    }

    boolean crosses(XBitSet vs, ArrayList<XBitSet> components) {
      int count = 0;
      for (XBitSet compo: components) {
        if (vs.intersects(compo)) {
          count++;
        }
      }
      return count >= 2;
    }

 
    void inheritAvailables() {
      reducerMap = new HashMap<>();
      for (Edge e: parent.reducerMap.keySet()) {
        int u = iMinor.map[e.u];
        int v = iMinor.map[e.v];
        Edge e1 = new Edge(u, v, h.n);
        assert 0 <= u && u < h.n && 0 <= v && v < h.n: u + ", " + v + ": " + h.n;
        reducerMap.put(e1, parent.reducerMap.get(e));
      }
      
      Set<Edge> inherited = new HashSet<>();
      for (Edge e: parent.availables) {
        int u = iMinor.map[e.u];
        int v = iMinor.map[e.v];
        if (u != v) {
          assert 0 <= u && u < h.n && 0 <= v && v < h.n: u + ", " + v + ": " + h.n +
              " " + e.u + ", " + e.v + " : " + parent.h.n;
          Edge e1 = new Edge(u, v, h.n);
          if (reducerMap.get(e1) == null) {
            inherited.add(e1);
          }
        }
      }
      availables = new ArrayList<>(inherited);
      sortAvailables();
    }

    void sortAvailables() {
      Map<Edge, EdgeValue> evalMap = new HashMap<>();
      for (Edge e: availables) {
        EdgeValue ev = new EdgeValue(e, h);
        ev.evaluate();
        evalMap.put(e, ev);
      }
      availables.sort((e1, e2) -> 
      evalMap.get(e1).compareTo(evalMap.get(e2)));
    }

    boolean importFrom(Node node) {
      if (TRACE_DETAIL) {
        System.out.println(indent() + "importing from " + node);
        System.out.println(indent() + "ub " + ub() + " node.ub " + node.ub());
      }
      Minor minor1 = node.minor.rebase(minor);
      UncontractionBT ubt = new UncontractionBT(h, minor1, 
          node.pidi.conducives(h.n * N_CONDUCIVES_RATIO));
      int oldUB = ub();
      TreeDecomposition td1 = ubt.firstTD();

      if (TRACE_DETAIL) {
        if (td1 == null) {
          System.out.println(indent() + "first td null");
        }
        else {
          System.out.println(indent() + "first td width " + td1.width);
        }
      }
      if (td1 == null) {
        return false;
      }
      while (td1 != null) {
        Graph cg = h.copy();
        for (XBitSet bag: td1.setOfBags()) {
          cg.fill(bag);
        }
        SemiPIDConstr spidIncr = new SemiPIDConstr(h, cg);
        spidIncr.decideWidth();
        Set<XBitSet> pmcs = spidIncr.usefulPMCs();
        pidi.importPMCs(pmcs);
        if (ub() < oldUB) {
          if (TRACE) {
            System.out.println(indent() + "importing lowered ub " + this);
          }
          return true;
        }
        td1 = ubt.anotherTD();
      }
      return ub() < oldUB;
    }
  
    void improveUB() {
      if (TRACE) {
        System.out.println(indent() + "improveUB " + this 
            + ", " + (System.currentTimeMillis() - t0) + " millisecs");
      }
      if (ub() <= kTarget) {
        return;
      }

      Block safe = findSafeBlock();
      if (safe != null) {
        processSafeSeparator(safe);
        return;
      }
      
      if (ub() <= kTarget) {
        if (TRACE_DETAIL) {
          System.out.println(indent() + "ub lowered by initial improving");
        }
        return;
      }

      for (Edge e: reducerMap.keySet()) {
        if (e.u == e.v) {
          Node node = reducerMap.get(e);
          assert node.minor.isAnUncontractionOf(minor);
          inheritPMCs(node);
          assert ub() < root.ub();
          if (TRACE) {
            System.out.println(indent() + "ub lowered because a reducing edge has been contracted");
          }
          return;
        }
        
        Node child = new Node(this, e, reducerMap.get(e));
        if (TRACE_DETAIL) {
          System.out.println("trying reducer child " + child);
        }
        importFrom(child);
        if (ub() <= kTarget) {
          if (TRACE) {
            System.out.println(indent() + "ub lowered by reducer child " + child);
          }
          return;
        }
      }

      nChild = 0;
      while (!availables.isEmpty()) {
        Edge e = availables.get(0);
        availables.remove(e);
        child = new Node(this, e);
        child.improveUB();
        assert child.ub() <= kTarget || gLB == root.ub();
        if (gLB == root.ub()) {
          return;
        }
        nChild++;
        reducerMap.put(e, child);
        
        assert child.pidi != null;
        importFrom(child);

        if (ub() <= kTarget) {
          if (TRACE_DETAIL) {
            System.out.println(indent() + "ub lowered by importing, returning " + this + ", " +  
                (System.currentTimeMillis() - t0) + " millisecs"); 
          }
          return;
        }
        pidi.improve(UNIT_BUDGET_UB * nChild);
        if (ub() <= kTarget) {
          if (TRACE) {
            System.out.println(indent() + "ub lowered by importing and improving, returning " + this + ", " +  
                (System.currentTimeMillis() - t0) + " millisecs"); 
          }
          return;
        }
        if (TRACE) {
          System.out.println(indent() + "ub failed to be lowered by importing " + this + ", " +  
              (System.currentTimeMillis() - t0) + " millisecs"); 
        }
      }
      if (TRACE) {
        System.out.println(indent() + "finishing pidi " +  
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      
      pidi.finish();
      
      if (ub() <= kTarget) {
        if (TRACE) {
          System.out.println(indent() + "ub lowered by finishing " + 
              (System.currentTimeMillis() - t0) + " millisecs");
        }
        return;
      }

      if (TRACE) {
        System.out.println(indent() + "infeasibility established " + pidi.nTicks + " ticks " + 
            (System.currentTimeMillis() - t0) + " millisecs");
      }
      gLB = kTarget + 1;
      obs = minor;
      return;
    }

    Set<XBitSet> minSeps(Graph h, int k) {
      MinSepsGenerator msg = new MinSepsGenerator(h, k);
      msg.generate();
      return msg.minSeps;
    }

    Set<XBitSet> uncontract(Set<XBitSet> separators, Minor minor) {
      Set<XBitSet> seps = new HashSet<>();
      for (XBitSet sep: separators) {
        seps.add(uncontract(sep, minor));
      }
      return seps;
    }
    
    XBitSet uncontract(XBitSet sep, Minor minor) {
      XBitSet u = new XBitSet();
      for (int v: sep.toArray()) {
        u.or(minor.components[v]);
      }
      return u;
    }

    void setLB(int lb) {
      setLB(lb, false);
    }
 
    void setLB(int lb, boolean minimalize) {
      if (TRACE) {
        System.out.println(indent() + "new LB " + lb);
      }
      gLB = lb;
      if (minimalize) {
        MinimalObstruction mo = new MinimalObstruction(h, lb - 1);
        obs = mo.minimal().composeWith(minor);  
      }
      else {
        obs = minor;
      }
    }
    
    Set<XBitSet> pmcsFromTDs(ArrayList<TreeDecomposition> tds) {
      Set<XBitSet> pmcs = new HashSet<>();
      for (TreeDecomposition td: tds) {
        pmcs.addAll(td.setOfBags());
      }
      return pmcs;
    }

    boolean equivalent(Edge e, Edge f, Minor minor) {
      return minor.map[e.u] == minor.map[f.u] && minor.map[e.v] == minor.map[f.v] ||
          minor.map[e.u] == minor.map[f.v] && minor.map[e.v] == minor.map[f.u];
    }

    void processSafeSeparator(Block block) {
      if (TRACE) {
        System.out.println(indent() + "Safe sep found " + 
            block.separator + ", comopnent " + block.component);
      }

      child = new Node(this, block);
      assert child.td != null;
      XBitSet sep = block.separator.convert(child.iMinor.map);
      assert child.h.isClique(sep);

      child.improveUB();
      
      if (child.ub() == root.ub()) {
        assert child.ub() == gLB;
        return;
      }

      if (TRACE) {
        System.out.println(indent() + "child width improved for the safe sep child " + child);
      }

      Set<XBitSet> pmcs = importPMCsViaSafeSep(child, block);
      if (TRACE) {
        System.out.println(indent() + "imported from safe sep child, this: " + this);
      }
      pidi = new PIDIterative(h, kTarget);
      pidi.importPMCs(pmcs);
      assert ub() == child.ub();
      return;
    }


    Block findSafeBlock() {
      for (int v = 0; v < h.n; v++) {
        Block block = blockOn(v);
        if (block == null) {
          continue;
        }
        if (block.separator.cardinality() + 
            block.component.cardinality() <= gLB + 1 &&
            block.def == 0) {
          block.getContractions();
          return block;
        }
      }

      Graph treeOfTD = td.toTree();
      XBitSet treeNodes = treeOfTD.all.removeBit(0);
      XBitSet largeNodes = new XBitSet();
      for (int b : treeNodes.toArray()) {
        if (td.bagAt(b).cardinality() > gLB) {
          largeNodes.set(b);
        }
      }
      XBitSet smalls = treeNodes.subtract(largeNodes);
      for (int b : smalls.toArray()) {
        ArrayList<XBitSet> subtrees = treeOfTD.componentsOf(treeNodes.removeBit(b));
        for (XBitSet subtree: subtrees) {
          if (!subtree.intersects(largeNodes)) {
            Block block = new Block(td, b, subtree);
            if (block.def == 0) {
              block.getContractions();
              return block;
            }
          }
        }
      }
      return null;
    }


    TreeDecomposition aDecomposition() {
      return pidi.getTD();
    }

    Block blockOn(int v) {
      XBitSet sep = h.neighborSet[v];
      ArrayList<XBitSet> components = h.separatedComponents(sep.addBit(v));
      for (XBitSet compo: components) {
        XBitSet sep1 = h.neighborSet(compo);
        if (sep1.equals(sep)) {
          return new Block(sep, new XBitSet(new int[] {v}));
        }
        ArrayList<XBitSet> fulls = h.fullComponents(sep1);
        for (XBitSet full: fulls) {
          if (full.get(v)) {
            if (full.nextSetBit(0) == v &&
                h.isClique(full) &&
                h.isBiclique(sep1, full)) {
              return new Block(sep1, full);
            }
            else {
              return null;
            }
          }
        }
      }
      return null;
    }

    boolean isSafeSepChild() {
      return e == null;
    }

    Set<XBitSet> importPMCsViaSafeSep(Node child, Block block) {
      int[] map = inversionMap(child.iMinor, h.all.subtract(block.component));
      Set<XBitSet> imported = new HashSet<>();
      for (XBitSet pmc: child.pidi.pmcs()) {
        assert child.h.isPMC(pmc);
        assert h.isPMC(pmc.convert(map));

        imported.add(pmc.convert(map));
      }
      Set<XBitSet> fromBlock = block.pmcsForComponent();
      for (XBitSet pmc: fromBlock) {
        assert pmc.cardinality() <= gLB + 1;
        assert h.isPMC(pmc);
      }
      
      imported.addAll(fromBlock);
      return imported;
    }

    int[] inversionMap(Minor iMinor, XBitSet scope) {
      int[] map = new int[iMinor.m];
      Arrays.fill(map, -1);
      for (int v = 0; v < iMinor.m; v++) {
        XBitSet compo = iMinor.components[v];
        for (int w = scope.nextSetBit(0); w >= 0; w = scope.nextSetBit(w + 1)) {
          if (compo.get(w)) {
            map[v] = w;
            break;
          }
        }
        assert map[v] >= 0;
      }
      return map;
    }


    Edge edgeBetween(XBitSet compo1, XBitSet compo2) {
      for (int v: compo1.toArray()) {
        XBitSet nb = h.neighborSet[v].intersectWith(compo2);
        if (!nb.isEmpty()) {
          int w = nb.nextSetBit(0);
          return new Edge(v, w, h.n);
        }
      }
      return null;
    }

    XBitSet[] toArray(Collection<XBitSet> compos) {
      XBitSet[] ca = new XBitSet[compos.size()];
      return compos.toArray(ca);
    }

    int additionalVertex(XBitSet acs) {
      for (int v = acs.nextSetBit(0); v >= 0; v = acs.nextSetBit(v + 1)) {
        if (h.isClique(acs.removeBit(v))) {
          return v;
        }
      }
      return -1;
    }

    MSC findSafeSep(TreeDecomposition td) {
      SafeSeparators ss = new SafeSeparators(td.g, td, ub() - 1);
      return ss.findASafeSep();
    }

    int indexOf(Edge e, Edge[] ea) {
      for (int i = 0; i < ea.length; i++) {
        if (e.equals(ea[i])) {
          return i;
        }
      }
      return -1;
    }

    int depth() {
      if (parent == null) {
        return 0;
      }
      else {
        return parent.depth() + 1;
      }
    }
    
    String indent() {
      int d = g.n - h.n;
      return d + ":" + spaces(d % 50);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("Node n " + h.n + " nChild " + nChild + 
          " gLB " + gLB + ", ub " + ub() +  " kTarget " + kTarget);
      sb.append(" pmcs " + pidi.pmcMap.size());
      if (availables != null) {
        sb.append(" availabes " + availables.size());
      }
      return sb.toString();
    }

    Set<XBitSet> usefulSeparators(int k) {
      MinSepsGenerator msg = new MinSepsGenerator(h, k);
      msg.generate();
      Set<XBitSet> minSeps = msg.minSeps;
      Set<XBitSet> usefuls = new HashSet<>();
    
      boolean moving = true;
      while (moving && usefuls.size() < h.n * N_CONDUCIVES_RATIO) {
        moving = false;
        int nc = usefuls.size();
        SemiPID spid = new SemiPID(h, k, minSeps, false);
        TreeDecomposition td = spid.decompose();
        if (td == null) {
          return usefuls;
        }
        td = MinimalizeTD.minimalize(td);
        usefuls.addAll(td.setOfBags());
        moving = usefuls.size() > nc;
        XBitSet sep = mostBalancedMinSep(td);
        minSeps.remove(sep);
      }
      return usefuls;
    }
    
    Set<XBitSet> generateConducives(int k) {
      MinSepsGenerator msg = new MinSepsGenerator(h, k);
      msg.generate();
      return generateConducives(k, msg.minSeps);
    }
    
    Set<XBitSet> generateConducives(int k, Set<XBitSet> minSeps) {
      Set<XBitSet> conducives = new HashSet<>();
    
      boolean moving = true;
      while (moving && conducives.size() < h.n * 2) {
        moving = false;
        int nc = conducives.size();
        SemiPID spid = new SemiPID(h, k, minSeps, false);
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

    int largestCompoSize(XBitSet sep, Graph g) {
      ArrayList<XBitSet> components = g.separatedComponents(sep);
      return XBitSet.largest(components).cardinality();
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
    
    class Block implements Comparable<Block>{
      XBitSet separator;
      XBitSet component;
      TreeDecomposition td;
      Graph treeOfTD;
      XBitSet treeCompo;
      Subgraph sub;
      Minor rMinor;
      int def;
      Set<Edge> contractions;

      Block(XBitSet separator, XBitSet component) {
        this.separator = separator;
        this.component = component;
        XBitSet closure = component.unionWith(separator);
        sub = new Subgraph(h, closure);
        RootedMinorGreedy rmg = new RootedMinorGreedy(sub.h, separator.convert(sub.conv));

        rMinor = rmg.contract();
        
        int n = separator.cardinality();
        assert rMinor.m == n;
        int m = rMinor.getGraph().numberOfEdges();
        def = n * (n - 1) / 2 - m;
        if (def > 0 && def <= 2) {
          RootedMinorBoundedDepthBacktrack rmbt = 
              new RootedMinorBoundedDepthBacktrack(sub.h, separator.convert(sub.conv));
          rmbt.hasCliqueMinor();
          if (rmbt.rMinor != null) {
            rMinor = rmbt.rMinor;
            m = rMinor.getGraph().numberOfEdges();
            def = n * (n - 1) / 2 - m;
          }
        }
      }
      
      Block(TreeDecomposition td, int anchor, XBitSet treeCompo) {
        this.td = td;
        this.treeCompo = treeCompo;
        assert td.g == h;
        component = td.unionBags(treeCompo).subtract(td.bagAt(anchor));
        separator = h.neighborSet(component);
        assert separator.isSubset(td.bagAt(anchor));

        XBitSet closure = component.unionWith(separator);
        sub = new Subgraph(h, closure);
        RootedMinorGreedy rmg = new RootedMinorGreedy(sub.h, separator.convert(sub.conv));

        rMinor = rmg.contract();
        
        int n = separator.cardinality();
        assert rMinor.m == n;
        int m = rMinor.getGraph().numberOfEdges();
        def = n * (n - 1) / 2 - m;
      }


      Edge globalize(Edge e) {
        return new Edge(sub.inv[e.u], sub.inv[e.v], h.n);
      }
      
      Set<XBitSet> pmcsForComponent() {
        Set<XBitSet> pmcs = new HashSet<>();
        if (treeCompo == null) {
          pmcs.add(separator.unionWith(component));
        }
        else {
          for (int b : treeCompo.toArray()) {
            assert td.bagAt(b).cardinality() <= gLB + 1;
            pmcs.add(td.bagAt(b));
          }
        }
        return pmcs;
      }

      void getContractions() {
        contractions = new HashSet<>();
        Minor minor1 = new Minor(h);
        ArrayList<Edge> edges = h.edgeList();
        while (contractions.size() < sub.h.n - rMinor.m) {
          XBitSet sep = separator.convert(minor1.map);
          Minor minor2 = null;
          for (Edge e: edges) {
            int u = minor1.map[e.u];
            int v = minor1.map[e.v];
            if (u == v) {
              continue;
            }
            if (!(sep.get(u) && component.get(e.v)||
                sep.get(v) && component.get(e.u))) {
              continue;
            }
            int u2 = sub.conv[e.u];
            int v2 = sub.conv[e.v];
            if (rMinor.map[u2] == rMinor.map[v2]) {
              minor2 = minor1.contract(u, v);
              contractions.add(e);
              break;
            }
          }
          assert minor2 != null;
          minor1 = minor2;
        }
        assert contractions.size() == sub.h.n - rMinor.m;
      }

      @Override
      public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("block sep " + separator + " comopnent " + component + " def " + def + 
            " contractions " + contractions);
        return sb.toString();
      }
      
      @Override
      public int compareTo(Block s) {
        if (def != s.def) {
          return def - s.def;
        }
        return XBitSet.cardinalityComparator.compare(separator, s.separator);
      }
    }
  }
     
  Edge[] toArray(Collection<Edge> edges) {
    Edge[] ea = new Edge[edges.size()];
    edges.toArray(ea);
    return ea;
  }

  static String digit(int n) {
    String d = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    if (n < d.length()) {
      return "" + d.charAt(n);
    }
    else return "(" + n + ")"; 
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
    if (h.n <= k + 1) {
      return true;
    }
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

//    test("../instance/PACE2017bonus_gr/", "Promedus_38_14", 0);    
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 0);    

//      test("../instance/he2017secret", "he012", 0);
    
//    test1("../instance/PACE2017bonus_gr/", "atco_enc2_opt2_10_21.gaifman_3", 0, "_bonushard_");
//    test("../instance/PACE2017bonus_gr/", "modgen-n200-m90860q08c40-1585.gaifman_2", 0);
//    test1("../instance/PACE2017bonus_gr/", "Promedas_62_11", 0, "_bonushard_");
//    test1("../instance/PACE2017bonus_gr/", "Promedas_48_11", 0, "_bonushard_");
//    test1("../instance/PACE2017bonus_gr/", "Promedas_44_11", 0, "_bonushard_");
//  test1("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0, "_retry_");
    
//    test("../instance/PACE2017bonus_gr/", "Sz512_15127_1.smt2-stp212.gaifman_3", 0);
//    test("../instance/PACE2017bonus_gr/", "MD5-32-1.gaifman_4", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_69_9", 0);
//    test("../instance/PACE2017bonus_gr/", "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_12", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_56_8", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_48_5", 0);
//    test("../instance/PACE2017bonus_gr/", "minxor128.gaifman_2", 0);
//    test("../instance/PACE2017bonus_gr/", "Promedas_49_8", 0);
//    test("../instance/PACE2017bonus_gr/", "FLA_14", 0);
//    test("../instance/PACE2017bonus_gr/", "post-cbmc-aes-d-r2.gaifman_10", 0);
//    test("../instance/PACE2017bonus_gr/", "FLA_13", 0);
//    test("../instance/PACE2017bonus_gr/", "mrpp_4x4#8_8.gaifman_3", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_14", 0); 
//    test("../instance/PACE2017bonus_gr/", "Promedus_34_11", 0);
//    test("../instance/PACE2017bonus_gr/", "countbitsarray04_32.gaifman_10", 0);
//  test("../instance/PACE2017bonus_gr/", "Promedus_27_15", 0);
//    test("../instance/PACE2017bonus_gr/", "aes_24_4_keyfind_5.gaifman_4", 0);
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
//    test("../instance/pace17exact/", "ex002", 0);
//    test("../instance/pace17exact/", "ex008", 0);
//    test("../instance/pace17exact/", "ex047", 0);
//    test("../instance/pace17exact/", "ex074", 0);
//    test("../instance/pace17exact/", "ex084", 0);
//    test("../instance/pace17exact/", "ex039", 0);
//    test("../instance/pace17exact/", "ex118", 0);    
  }

  private static void test(String path, String name, int width) {
    test1(path, name, width, "");
  }
  
  private static void test1(String path, String name, int width, String suff) {
    log = new Log("ContractionRecursiveUB" + suff +
        ContractionRecursive.VERSION + "_" + 
        ContractionRecursive.UNIT_BUDGET_UB + " "+  
        ContractionRecursive.N_CONDUCIVES_RATIO, 
        name);

    Graph g = Graph.readGraph(path, name);

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

    ContractionRecursive crubr = new ContractionRecursive(local.h);
    TreeDecomposition td = crubr.decompose();
    log.log(name + " width " + td.width + " " + 
    (System.currentTimeMillis() - t0) + " millisecs");
    crubr.obs.getGraph().save("obs_" + name + ".gr");
  }
}
