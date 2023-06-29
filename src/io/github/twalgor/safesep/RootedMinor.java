package io.github.twalgor.safesep;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.XBitSet;

public abstract class RootedMinor {
  Graph g;
  XBitSet root;
  
  public RootedMinor(Graph g, XBitSet root) {
    this.g = g;
    this.root = root;
  }
  
  public abstract boolean hasCliqueMinor();

}
