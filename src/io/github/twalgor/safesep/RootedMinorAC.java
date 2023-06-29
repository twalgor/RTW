package io.github.twalgor.safesep;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.XBitSet;

public class RootedMinorAC extends RootedMinor {

  public RootedMinorAC(Graph g, XBitSet root) {
    super(g, root);
  }
  
  @Override
  public boolean hasCliqueMinor() {
    XBitSet rest = g.all.subtract(root);
    assert g.isConnected(rest);
    assert g.neighborSet(rest).equals(root);
    
    return g.isAlmostClique(root);
  }

}
