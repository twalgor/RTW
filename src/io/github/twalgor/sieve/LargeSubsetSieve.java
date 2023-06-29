package io.github.twalgor.sieve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.XBitSet;


public class LargeSubsetSieve {
  static enum NodeType {
    BYTE, SHORT, INT, LONG, LEAF
  }

  int[] typeLength = new int[] 
      {Byte.BYTES, Short.BYTES, Integer.BYTES,  Long.BYTES, 0};

  private static final int NODE_SIZE = 20000;
//  private static boolean VERIFY = true;
  private static boolean VERIFY = false;
//  private static boolean DEBUG = true;
  private static boolean DEBUG = false;
//  private static boolean COUNT = true;
  private static boolean COUNT = false;
  
  int n;
  int depth;
  
  Node root;

  HashSet<XBitSet> sieved;
   
  public LargeSubsetSieve (int n) {
//    System.out.println("n = " + n);
    this.n = n;
    depth = (n - 1) / 8 + 1;
    if (VERIFY) {
      sieved = new HashSet<>();
    }
    root = null;
    if (DEBUG) {
      System.out.println("Large subset sieve created for n = " + n);
    }
  }

  public void add(XBitSet set) {
    if (VERIFY) {
      sieved.add(set);
    }
    if (root == null) {
      root = newEntry(0, set.toByteArray(), set);  
    }
    else {
      root.add(set.toByteArray(), set);
    }
    
    if (DEBUG) {
      System.out.println("added " + set);
      root.dump("");
    }
  }

  Node newEntry(int d, byte[] bytes, XBitSet set) {
    if (d == depth) {
      Node result = new Node(d, NodeType.LEAF, null, null);
      result.set = set;
      return result;
    }
    int length;
    NodeType type;
    if (depth - d >= Long.BYTES) {
      type = NodeType.LONG;
      length = Long.BYTES;
    }
    else if (depth - d >= Integer.BYTES) {
      type = NodeType.INT;
      length = Integer.BYTES;
    }
    else if (depth - d >= Short.BYTES) {
      type = NodeType.SHORT;
      length = Short.BYTES;
    }
    else {
      type = NodeType.BYTE;
      length = 1;
    }
    long label = 0;
    for (int i = length - 1; i >= 0; i--) {
       label = label << 8;
       if (d + i < bytes.length) { 
         label |= bytes[d + i] & 0xff;
       }
    }
    
    Object labels = null;
    
    switch (type) {
    case BYTE:
      labels = new byte[] {(byte) (label & 0xff)};
      break;
    case SHORT:
      labels = new short[] {(short) (label & 0xffff)};
      break;
    case INT:
      labels = new int[] {(int) (label & 0xffffffff)};
      break;
    case LONG:
      labels = new long[] {label};
      break;
    default:
      break;
    }
    
    Node result = new Node(d, type, labels, new Node[] {
        newEntry(d + length, bytes, set)});

    return result;
  }
  
  public ArrayList<XBitSet> get(XBitSet sup, int maxMissing) {
    ArrayList<XBitSet> result = new ArrayList<>();
    if (root == null) {
      return result;
    }
    root.get(sup.toByteArray(), maxMissing, result);

    if (VERIFY) {
      Set<XBitSet> rSet = new HashSet<>();
      rSet.addAll(result);
      Set<XBitSet> correct = new HashSet<>();
      for (XBitSet set: sieved) {
        if (set.isSubset(sup) && sup.subtract(set).cardinality() <= maxMissing) {
          correct.add(set);
        }
      }
      boolean isCorrect = true;
      for (XBitSet set: correct) {
        if (!rSet.contains(set)) {
          isCorrect = false;
          System.out.println("missing " + set + 
              " for get(" + sup + "," + maxMissing + ")");
        }
      }
      for (XBitSet set: rSet) {
        if (!correct.contains(set)) {
          isCorrect = false;
          System.out.println("extra " + set + 
              " for get(" + sup + "," + maxMissing + ")");
        }
      }
      if (!isCorrect) {
        dump();
      }
    }
    return result;
  }
  
  void dump() {
    System.out.println("sieve for n = " + n);
    if (root == null) {
        System.out.println(" empty");
    }
    else {
      root.dump("");
    }
  }
   
  class Node {
    int d;
    NodeType type;
    Object labels;
    Node[] children;
    XBitSet set;
    
    Node(int d, NodeType type, Object labels, Node[] children) {
      this.d = d;
      this.type = type;
      this.labels = labels;
      this.children = children;
    }

    void add(byte[] setBytes, XBitSet set) {
      switch (type) {
      case BYTE: {
        byte[] bytes = (byte[]) labels;
        byte b = 0;
        if (d < setBytes.length) {
          b = setBytes[d];
        }
        int i = Arrays.binarySearch(bytes, b); 
        if (i >= 0) {
          children[i].add(setBytes, set);
        }
        else {
          i = -i - 1;
          byte[] tmp = new byte[bytes.length + 1];
          System.arraycopy(bytes, 0, tmp, 0, i);
          System.arraycopy(bytes, i, tmp, i + 1, bytes.length - i);
          tmp[i] = b;
          labels = tmp;
          Node[] ctmp = new Node[children.length + 1];
          System.arraycopy(children, 0, ctmp, 0, i);
          System.arraycopy(children, i, ctmp, i + 1, children.length - i);
          ctmp[i] = newEntry(d + 1, setBytes, set);
          children = ctmp;
        }
        break;
      }
      case SHORT: {
        short label = 0;
        for (int j = Short.BYTES - 1; j >= 0; j--) {
           label = (short) (0xffff & (label << 8));
           if (d + j < setBytes.length) { 
             label |= setBytes[d + j] & 0xff;
           }
        }

        short[] shorts = (short[]) labels;
        int i = Arrays.binarySearch(shorts, label);
        if (i >= 0) {
          children[i].add(setBytes, set);
        }
        else {
          i = -i - 1;
          short[] tmp = new short[shorts.length + 1];
          System.arraycopy(shorts, 0, tmp, 0, i);
          System.arraycopy(shorts, i, tmp, i + 1, shorts.length - i);
          tmp[i] = label;
          labels = shorts = tmp;
          Node[] ctmp = new Node[children.length + 1];
          System.arraycopy(children, 0, ctmp, 0, i);
          System.arraycopy(children, i, ctmp, i + 1, children.length - i);
          ctmp[i] = newEntry(d + Short.BYTES, setBytes, set);
          children = ctmp;
          if (shorts.length > NODE_SIZE) {
            splitShort();
          }
        }
        break;
      }
      case INT: {
        int label = 0;
        for (int j = Integer.BYTES - 1; j >= 0; j--) {
           label = label << 8;
           if (d + j < setBytes.length) { 
             label |= setBytes[d + j] & 0xff;
           }
        }
        int[] ints = (int[]) labels;
        int i = Arrays.binarySearch(ints, label);
        if (i >= 0) {
          children[i].add(setBytes, set);
        }
        else {
          i = -i - 1;
          int[] tmp = new int[ints.length + 1];
          System.arraycopy(ints, 0, tmp, 0, i);
          System.arraycopy(ints, i, tmp, i + 1, ints.length - i);
          tmp[i] = label;
          labels = ints = tmp;
          Node[] ctmp = new Node[children.length + 1];
          System.arraycopy(children, 0, ctmp, 0, i);
          System.arraycopy(children, i, ctmp, i + 1, children.length - i);
          ctmp[i] = newEntry(d + Integer.BYTES, setBytes, set);
          children = ctmp;
          if (ints.length > NODE_SIZE) {
            splitInt();
          }
        }
        break;
      }
      case LONG: {
        long label = 0;
        for (int j = Long.BYTES - 1; j >= 0; j--) {
           label = label << 8;
           if (d + j < setBytes.length) { 
             label |= setBytes[d + j] & 0xff;
           }
        }
        long[] longs = (long[]) labels;
        int i = Arrays.binarySearch(longs, label);
        if (i >= 0) {
          children[i].add(setBytes, set);
        }
        else {
          i = -i - 1;
          long[] tmp = new long[longs.length + 1];
          System.arraycopy(longs, 0, tmp, 0, i);
          System.arraycopy(longs, i, tmp, i + 1, longs.length - i);
          tmp[i] = label;
          labels = longs = tmp;
          Node[] ctmp = new Node[children.length + 1];
          System.arraycopy(children, 0, ctmp, 0, i);
          System.arraycopy(children, i, ctmp, i + 1, children.length - i);
          ctmp[i] = newEntry(d + Long.BYTES, setBytes, set);
          children = ctmp;
          if (longs.length > NODE_SIZE) {
            splitLong();
          }

        }
        break;
      }
      case LEAF:
        break;
      }
      return;
    }
    
    void splitShort() {
      short[] shorts = (short[]) labels;
      byte[] bytes = new byte[shorts.length];
      Node[] newChildren = new Node[shorts.length];
      int k = 0;
      int s = 0;
      while (s < shorts.length) {
        byte b = (byte) (shorts[s] & 0xff);
        int m = s + 1;
        while (m < shorts.length && 
            (byte) (shorts[m] & 0xff) == b) m++;
        byte[] cBytes = new byte[m - s];
        Node[] cChildren = new Node[m - s];
        for (int i = 0; i < m - s; i++) {
          cBytes[i] = (byte) ((shorts[s + i] >> 8) & 0xff);
          cChildren[i] = children[s + i];
        }
        type = NodeType.BYTE;
        bytes[k] = b;
        newChildren[k] = new Node(d + Byte.BYTES, NodeType.BYTE, cBytes, cChildren);
        k++;
        s = m;
      }
      labels = Arrays.copyOf(bytes, k);
      children = Arrays.copyOf(newChildren, k);
     }
    
    void splitInt() {
      int[] ints = (int[]) labels;
      short[] shorts = new short[ints.length];
      Node[] newChildren = new Node[ints.length];
      int k = 0;
      int s = 0;
      while (s < ints.length) {
        short b = (short) (ints[s] & 0xffff);
        int m = s + 1;
        while (m < ints.length && 
            (short) (ints[m] & 0xffff) == b) m++;
        short[] cShorts = new short[m - s];
        Node[] cChildren = new Node[m - s];
        for (int i = 0; i < m - s; i++) {
          cShorts[i] = (short) ((ints[s + i] >> 16) & 0xffff);
          cChildren[i] = children[s + i];
        }
        shorts[k] = b;
        newChildren[k] = new Node(d + Short.BYTES, NodeType.SHORT, cShorts, cChildren);
        k++;
        s = m;
      }
      type = NodeType.SHORT;
      labels = Arrays.copyOf(shorts, k);
      children = Arrays.copyOf(newChildren, k);
    }
    
    void splitLong() {
      long[] longs = (long[]) labels;
      int[] ints = new int[longs.length];
      Node[] newChildren = new Node[longs.length];
      int k = 0;
      int s = 0;
      while (s < longs.length) {
        int b = (int) (longs[s] & 0xffffffff);
        int m = s + 1;
        while (m < longs.length && 
            (int) (longs[m] & 0xffff) == b) m++;
        int[] cInts = new int[m - s];
        Node[] cChildren = new Node[m - s];
        for (int i = 0; i < m - s; i++) {
          cInts[i] = (int) ((longs[s + i] >> 32) & 0xffffffff);
          cChildren[i] = children[s + i];
        }
        ints[k] = b;
        newChildren[k] = new Node(d + Integer.BYTES, NodeType.INT, cInts, cChildren);
        k++;
        s = m;
      }
      type = NodeType.INT;
      labels = Arrays.copyOf(ints, k);
      children = Arrays.copyOf(newChildren, k);
    }
    
    void get(byte[] supBytes, int maxMissing, ArrayList<XBitSet> result) {
      if (type == NodeType.LEAF) {
        result.add(set);
        return;
      }
      
      if (type == NodeType.BYTE) {
        byte sup = 0;
        if (d < supBytes.length) {
            sup = supBytes[d];
        }
        byte[] bytes = (byte[]) labels;
        for (int i = 0; i < bytes.length; i++) {
          if (((bytes[i] & ~sup) & 0xff) == 0) {
            int missing = sup & ~bytes[i];
            int nMiss = Integer.bitCount(missing);
            if (nMiss <= maxMissing)
            children[i].get(supBytes, maxMissing - nMiss, result);
          }
        }
      }
      
      int length = typeLength[type.ordinal()];

      long lsup = 0;
      for (int i = length - 1; i >= 0; i--) {
         lsup = lsup << 8;
         if (d + i < supBytes.length) { 
           lsup |= supBytes[d + i] & 0xff;
         }
      }
      
      switch (type) {
      case SHORT: {
        short sup = (short) (0xffff & lsup);
        
        short[] shorts = (short[]) labels;
        for (int i = 0; i < shorts.length; i++) {
          if (((shorts[i] & ~sup) & 0xffff) == 0) {
            int missing = sup & ~shorts[i];
            int nMiss = Integer.bitCount(missing);
            if (nMiss <= maxMissing)
            children[i].get(supBytes, maxMissing - nMiss, result);
          }
        }
        break;
      }
      case INT: {
        int sup = (int) (0xffffffff & lsup);
        
        int[] ints = (int[]) labels;
        for (int i = 0; i < ints.length; i++) {
          if ((ints[i] & ~sup) == 0) {
            int missing = sup & ~ints[i];
            int nMiss = Integer.bitCount(missing);
            if (nMiss <= maxMissing)
            children[i].get(supBytes, maxMissing - nMiss, result);
          }
        }
        break;
      }
      case LONG: {
        long[] longs = (long[]) labels;
        for (int i = 0; i < longs.length; i++) {
          if ((longs[i] & ~lsup) == 0) {
            long missing = lsup & ~longs[i];
            int nMiss = Long.bitCount(missing);
            if (nMiss <= maxMissing)
            children[i].get(supBytes, maxMissing - nMiss, result);
          }
        }
        break;
      }
      }
    }
    void dump(String indent) {
      System.out.print(indent + d + " " + type);
      switch (type) {
      case BYTE: {
        System.out.println();
        byte[] bytes = (byte[]) labels;
        for (int i = 0; i < bytes.length; i++) {
          System.out.println(indent + ascendingBynary(bytes[i], 8));
          children[i].dump(indent + " ");
        }
        break;
      }
      case SHORT: {
        System.out.println();
        short[] shorts = (short[]) labels;
        for (int i = 0; i < shorts.length; i++) {
          System.out.println(indent + ascendingBynary(shorts[i], 16));
          children[i].dump(indent + " ");
        }
        break;
      }
      case INT: {
        System.out.println();
        int[] ints = (int[]) labels;
        for (int i = 0; i < ints.length; i++) {
          System.out.println(indent + ascendingBynary(ints[i], 32));
          children[i].dump(indent + " ");
        }
        break;
      }
      case LONG: {
        System.out.println();
        long[] longs = (long[]) labels;
        for (int i = 0; i < longs.length; i++) {
          System.out.println(indent + ascendingBynary(longs[i], 64));
          children[i].dump(indent + " ");
        }
        break;
      }
      case LEAF: {
        System.out.println(" " + set);
      }
      }
    }
  }
  
  String ascendingBynary(long s, int n) {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < n; i++) {
      if ((s & 1) == 0) sb.append("0");
      else sb.append("1");
      s = s >> 1;
    }
    return sb.toString();
  }

  String ascendingBynary(int s, int n) {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < n; i++) {
      if ((s & 1) == 0) sb.append("0");
      else sb.append("1");
      s = s >> 1;
    }
    return sb.toString();
  }
  
  static void test(int n, int ns, int nMiss, int m) {
    Random random = new Random(1);
    LargeSubsetSieve lSieve = new LargeSubsetSieve(n);
    for (int i = 0; i < m; i++) {
      int s = random.nextInt(ns) + 1;
      XBitSet toAdd = randomSubset(n, s, random);
      System.out.println("adding " + toAdd);
      lSieve.add(toAdd);
      int qs = random.nextInt(n) + 1;
      XBitSet querySet = randomSubset(n, qs, random);
      System.out.println("query " + querySet + ", " + nMiss);
      ArrayList<XBitSet> got = lSieve.get(querySet, nMiss);
      System.out.println(got.size());
    }
  }
  
  static XBitSet randomSubset(int n, int s, Random random) {
    XBitSet result = new XBitSet(n);
    for (int i = 0; i < n; i++) {
      if (random.nextInt(n - i) < s) {
        result.set(i);
        s--;
      }
    }
    return result;
  }
  
  public static void main(String[] args) {
//    test(10, 3, 4, 10);
    test(100, 40, 50, 10000);
  }
}