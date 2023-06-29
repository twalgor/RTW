package io.github.twalgor.common;

public class EdgeSet {
  public int n;
  XBitSet[] adjacency;
  public int m;
  
  public EdgeSet(int n) {
    this.n = n;
    adjacency = new XBitSet[n];
    m = 0;
  }
  
  public EdgeSet(Graph g) {
    this.n = g.n;
    adjacency = new XBitSet[n];
    for (int v = 0; v < n; v++) {
      adjacency[v] = (XBitSet) g.neighborSet[v].clone(); 
      adjacency[v].clear(0, v);
      m += adjacency[v].cardinality();
    }
  }
  
  public EdgeSet convert(int[] conv) {
    EdgeSet es = new EdgeSet(n);
    for (int i = 0; i < m; i++) {
      int[] e = getEdgeAt(i);
      int u = conv[e[0]];
      int v = conv[e[1]];
      if (u != v) {
        es.set(u,  v);
      }
    }
    return es;
  }
  
  public boolean get(int v, int w) {
    if(v > w) {
      return get(w, v);
    }
    if (adjacency[v] == null) {
      return false;
    }
    else return adjacency[v].get(w);
  }

  public boolean set(int v, int w) {
    if (v > w) {
      return set(w, v);
    }
    if (adjacency[v] == null) {
      adjacency[v] = new XBitSet(n);
      adjacency[v].set(w);
      m++;
      return true;
    }
    else if (adjacency[v].get(w)) {
      return false;
    }
    else {
      adjacency[v].set(w);
      m++;
      return true;
    }
  }

  public boolean remove(int v, int w) {
    if (v > w) {
      return remove(w, v);
    }
    if (adjacency[v] == null) {
      return false;
    }
    else if (adjacency[v].get(w)) {
      adjacency[v].clear(w);
      m--;
      return true;
    }
    else {
      return false;
    }
  }
  
  public int[] getEdgeAt(int i) {
    int count = 0;
    for (int v = 0; v < n; v++) {
      if (adjacency[v] != null) {
        int c = adjacency[v].cardinality();
        if (i < count + c) {
          return new int[] {v, adjacency[v].toArray()[i - count]};
        }
        else {
          count += c;
        }
      }
    }
    return null;
  }
  
  public boolean hasEdgeIn(XBitSet vs) {
    for (int v = vs.nextSetBit(0); v >= 0; v = vs.nextSetBit(v + 1)) {
      if (adjacency[v] != null &&
          adjacency[v].intersects(vs)) {
        return true;
      }
    }
    return false;
  }
  
  public void removeContained(XBitSet vs) {
    for (int v = vs.nextSetBit(0); v >= 0; v = vs.nextSetBit(v + 1)) {
      if (adjacency[v] != null) {
        m -= adjacency[v].intersectWith(vs).cardinality();
        adjacency[v].andNot(vs);
      }
    }
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(m + "{");
    int count = 0;
    for (int v = 0; v < n; v++) {
      for (int w = adjacency[v].nextSetBit(0); w >= 0;
          w = adjacency[v].nextSetBit(w + 1)) {
        if (count > 0) {
          sb.append(",");
        }
        sb.append("(" + v + "," + w + ")");
        count++;
      }
    }
    sb.append("}");
    assert count == m;
    return sb.toString();
  }
  
}
