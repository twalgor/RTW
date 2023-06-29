package io.github.twalgor.decomposer;

import java.util.LinkedList;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.TreeDecomposition;
import io.github.twalgor.common.XBitSet;
import io.github.twalgor.minseps.MinSepsGenerator;

public class ResourceBoundedSolverOld {
  static final boolean TRACE = true;
  static final int N_RECORD = 10;
  int nMinSeps;
  LinkedList<Record> records;
  Graph g;
  int k;
  Set<XBitSet> minSeps;
  SemiPID spid;
  
  public ResourceBoundedSolverOld(int nMinSeps) {
    this.nMinSeps = nMinSeps;
    records = new LinkedList<>();
    if (TRACE) {
      System.out.println("Resource bounded solver created " + this);
    }
  }
  
  public boolean prepare(Graph g, int k) {
    this.g = g;
    this.k = k;
    
    if (TRACE) {
      System.out.println("preparing for " + g.n + " " + k + " " + this);
    }
    if (!records.isEmpty()) {
      int nms = estimate(g.n, k);
      if (TRACE) {
        System.out.println("estimate " + nms);
      }
      if (nms > nMinSeps) {
        return false;
      }
    }
    MinSepsGenerator msg = new MinSepsGenerator(g, k);
    msg.generate();
    minSeps = msg.minSeps;
    records.add(new Record(g.n, k, minSeps.size()));
    while (records.size() > N_RECORD) {
      records.remove();
    }
    return minSeps.size() <= nMinSeps;
  }
  
  int estimate(int n, int k) {
    int estimate = Integer.MAX_VALUE;
    for (Record r: records) {
      int est = r.estimate(n, k);
      if (est < estimate) {
        estimate = est;
      }
    }
    return estimate;
  }

  public boolean isFeasible() {
    spid = new SemiPID(g, k, minSeps, false);
    boolean isFeasible = spid.isFeasible();
    if (TRACE) {
      System.out.println("isFeasible " + isFeasible);
    }
    return isFeasible;
  }
  
  public TreeDecomposition getTD() {
    return spid.getTD();
  }
  
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("nMinSep " + nMinSeps);
    for (Record r: records) {
      sb.append(" " + r);
    }
    return sb.toString();
  }
  
  class Record {
    int n;
    int k;
    int nms;
    
    Record(int n, int k, int nms) {
      this.n = n;
      this.k = k;
      this.nms = nms;
    }
    
    int estimate(int n, int k) {
      int est = nms;
      if (n < this.n) {
        for (int i = n; i < this.n; i+= 2) {
          est /= 2;
        }
      }
      else if (n > this.n) { 
        for (int i = this.n; i < n; i += 2) {
          est *= 2;
          if (est > nMinSeps) {
            return est;
          }
        }
      }
      for (int i = this.k; i < k; i += 2) {
        est *= 2;
        if (est > nMinSeps) {
          return est;
        }
      }
      return est;
    }
    
    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("(");
      sb.append(n + " ");
      sb.append(k + " ");
      sb.append(nms + ")");
      return sb.toString();
    }
  }
}
