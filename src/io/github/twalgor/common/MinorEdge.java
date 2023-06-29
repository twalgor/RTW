package io.github.twalgor.common;

public class MinorEdge extends Edge {
  public Minor minor;
  public int id;
  
  public MinorEdge(int u, int v, Minor minor) {
    super(u, v, minor.m);
    this.minor = minor;
    XBitSet cu = minor.components[u];
    XBitSet cv = minor.components[v];

    id = -1;
    for (int x = cu.nextSetBit(0); x >= 0; x = cu.nextSetBit(x + 1)) {
      for (int y = cv.nextSetBit(0); y >= 0; y = cv.nextSetBit(y + 1)) {
        if (minor.g.areAdjacent(x, y)) {
          id = x * minor.g.n + y;
          break;
        }
      }
      if (id >= 0) {
        break;
      }
    }
    assert id >= 0;
  }
  

}
