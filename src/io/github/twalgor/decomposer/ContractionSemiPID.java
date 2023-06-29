package io.github.twalgor.decomposer;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import io.github.twalgor.common.Edge;
import io.github.twalgor.common.Graph;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.minseps.MinSepsGenerator;
import io.github.twalgor.sieve.SubblockSieve;

public class ContractionSemiPID {
  static final int LINE_LENGTH =50;
//  static final boolean VALIDATE = true;
  static final boolean VALIDATE = false;
//  static final boolean CONSTRUCT_TD = true;
static final boolean CONSTRUCT_TD = false;
//  static final boolean VERBOSE = true;
//  static final boolean VERBOSE = false;
  static final boolean TRACE = true;
//  static boolean TRACE = false;
//  static final boolean TRACE_ROOT = true;
  static final boolean TRACE_ROOT = false;
  
  Graph g;
  int k;
  Edge[] contEdges;
  
  XBitSet allCont;
  
  Set<XBitSet> minSeps;
  Map<XBitSet, Block> blockMap;
  
  SubblockSieve[] sieve;
  
  public Block all;

  public ContractionSemiPID(Graph g, int k, Set<XBitSet> minSeps, Edge[] contEdges) {
    this.g = g;
    this.k = k;
    this.minSeps = minSeps;
    this.contEdges = contEdges;
    allCont = XBitSet.all(contEdges.length);

  }

  public void dp() {
    blockMap = new HashMap<>();

    for (XBitSet sep: minSeps) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      for (XBitSet full: fulls) {
        if (isSmall(full)) {
          makeBlock(full);
        }
      }
    }

    Block[] ba = blockMap.values().toArray(new Block[blockMap.values().size()]);
    Arrays.sort(ba, (b1, b2) -> 
      XBitSet.cardinalityComparator.compare(b1.component, b2.component));

    sieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      sieve[v] = new SubblockSieve(g, k + 1);
    }

    for (Block block: ba) {
      block.decideFeasibility();
      if (!block.feasibility.isEmpty()) {
        if (TRACE) {
          System.out.println(block.indent() + block);
        }
        sieve[block.component.nextSetBit(0)].add(block.component, block.separator);
      }
    }
    all = new Block(g.all);
    all.decideFeasibility();
  }
  
  boolean isSmall(XBitSet component) {
    return 2 * component.cardinality() <= 
        g.n - (g.neighborSet(component).cardinality());
  }


  String indent(XBitSet compo) {
    return spaces((g.n - compo.cardinality()) * LINE_LENGTH / g.n);
  }
  
  Block makeBlock(XBitSet component) {
    Block block = blockMap.get(component);
    if (block == null) {
      block = new Block(component);
      blockMap.put(component, block);
    }
    return block;
  }
  
  XBitSet weight(XBitSet vertices) {
    XBitSet w = new XBitSet();
    for (int i = 0; i < contEdges.length; i++) {
      if (vertices.get(contEdges[i].u) && 
          vertices.get(contEdges[i].v)) {
        w.set(i);
      }
    }
    return w;
  }

  public class Block{
    XBitSet component;
    XBitSet separator;
    public XBitSet feasibility;

    Block(XBitSet component, XBitSet separator) {
      this.component = component;
      this.separator = separator;
    }

    Block(XBitSet component) {
      this.component = component;
      separator = g.neighborSet(component);
    }

    void decideFeasibility() {
      if (component.cardinality() + separator.cardinality() <= k) {
        feasibility = allCont;
        return;
      }
      
      else if (component.cardinality() + separator.cardinality() == k + 1) {
        feasibility = weight(component.unionWith(separator));
      }
      
      else {
        feasibility = new XBitSet();
      }

      decideFeasibility(component, separator, component);
    }
    
    void decideFeasibility(XBitSet compo, XBitSet sep, XBitSet scope) {
      int v0 = compo.nextSetBit(0);

      ArrayList<XBitSet> candidates = sieve[v0].get(compo, sep);
      for (XBitSet cand: candidates) {
        XBitSet candSep = g.neighborSet(cand);

        XBitSet union = separator.unionWith(candSep);
        assert !union.equals(sep);
        assert union.cardinality() <= k + 1;
        tryUnion(union, scope);
        if (feasibility.equals(allCont)) {
          return;
        }
      }
      if (sep.cardinality() <= k) {
        tryUnion(sep.addBit(v0), scope);
      }
    }


    void tryUnion(XBitSet union, XBitSet scope) {
      ArrayList<XBitSet> fulls = g.fullComponents(union);
      if (fulls.isEmpty() || fulls.size() >= 2) {
        XBitSet feas;
        if (union.cardinality() <= k) {
          feas = (XBitSet) allCont.clone();
        }
        else {
          feas = weight(union);
        }
        ArrayList<XBitSet> components = g.separatedComponents(union);
        for (XBitSet compo: components) {
          if (!compo.isSubset(scope)) {
            continue;
          }
          Block block = blockMap.get(compo);
          if (block == null) {
            feas.clear();
            break;
          }
          assert block.feasibility != null;
          feas.and(block.feasibility);
        }
        feasibility.or(feas);
        return;
      }
      if (union.cardinality() == k + 1) {
        return;
      }
      assert fulls.size() == 1;
      XBitSet full = fulls.get(0);
      decideFeasibility(full, union, scope);
    }

    String indent(XBitSet component) {
      return ContractionSemiPID.this.indent(component);
    }

    String indent() {
      return this.indent(component);
    }

    @Override
    public String toString() {
      return "feas " + feasibility + " sep " + separator + " compo " + component; 
    }
  }

  static String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }
  
}

