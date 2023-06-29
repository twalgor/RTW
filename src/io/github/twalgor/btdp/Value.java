package io.github.twalgor.btdp;

public class Value implements Comparable<Value>{
  public static final Value INFEASIBLE = new Value(Integer.MAX_VALUE, 0);
  public int width;
  public int rigidity;

  public Value(int width, int rigidity) {
    super();
    this.width = width;
    this.rigidity = rigidity;
  }
  
  public Value(Value value) {
    super();
    this.width = value.width;
    this.rigidity = value.rigidity;
  }

  public void add(Value v) {
    if (v.width > width) {
      width = v.width;
      rigidity = v.rigidity;
    }
    else if (v.width == width) {
      rigidity += v.rigidity;
    }
  }
  
  @Override
  public int compareTo(Value v) {
    if (width != v.width) {
      return width - v.width;
    }
    return rigidity - v.rigidity;
  }
  
  @Override
  public String toString() {
    if (this == INFEASIBLE) {
      return "INFEASIBLE";
    }
    return "(" + width + "," + rigidity + ")";
  }
  
  @Override
  public boolean equals(Object x) {
    Value val = (Value) x;
    return width == val.width && rigidity == val.rigidity;
  }
}

