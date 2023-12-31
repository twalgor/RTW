package io.github.twalgor.sieve;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import io.github.twalgor.common.Graph;
import io.github.twalgor.common.XBitSet;


public class SubblockSieve {
//  static boolean saveSieveSeq = false;
  static boolean saveSieveSeq = true;
  static enum NodeType {
    BYTE, SHORT, INT, LONG, LEAF
  }

  int[] typeLength = new int[] 
      {Byte.BYTES, Short.BYTES, Integer.BYTES,  Long.BYTES, 0};
  
  static final String sieveSequencePath = "sieveSequence2";

  private static final int NODE_SIZE = 20000;
//  private static boolean VERIFY = true;
  private static boolean VERIFY = false;
//  private static boolean DEBUG = true;
  private static boolean DEBUG = false;
//  private static boolean COUNT = true;
  private static boolean COUNT = false;
  
  Graph g;
  int n;
  int depth;
  
  // note that this width is exactly the total width bound
  // on the union of the scope and the component retrieved,
  // unlike previous versions where width + 1 is allowed.
  int width;
  
  Node[] root;

  HashMap<XBitSet, XBitSet> sieved;
  ArrayList<XBitSet> sieveSequence;
  PrintStream ssStream;
  
  int minElement;
   
  public SubblockSieve (Graph g, int width) {
//    System.out.println("n = " + n);
    this.g = g;
    this.n = g.n;
    depth = (n - 1) / 8 + 1;
    this.width = width;
    if (VERIFY) {
      sieved = new HashMap<>();
      sieveSequence = new ArrayList<>();
      try {
        ssStream = new PrintStream(new FileOutputStream(sieveSequencePath));
        ssStream.close();
        
      } catch (FileNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    root = new Node[width + 1];
    if (DEBUG) {
      System.out.println("Subblock sieve created for n = " + n + ", width = " + width);
    }
  }

  public void add(XBitSet component, XBitSet neighbors) {
    if (VERIFY) {
      sieved.put(component, neighbors);
      sieveSequence.add(component);
    }
    XBitSet closure = component.unionWith(neighbors);
    int nn = neighbors.cardinality();
    if (root[nn] != null) {
       root[nn].add(closure.toByteArray(), component);
    }
    else {
       root[nn] = newEntry(0, closure.toByteArray(), component);
    }
    if (DEBUG) {
      System.out.println("added, wdith = " +  nn + ": " + component + ", " + neighbors);
      root[nn].dump("");
    }
  }

  Node newEntry(int d, byte[] closureBytes, 
      XBitSet component) {
    if (d == depth) {
      Node result = new Node(d, NodeType.LEAF, null, null);
      result.component = component;
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
       if (d + i < closureBytes.length) { 
         label |= closureBytes[d + i] & 0xff;
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
        newEntry(d + length, closureBytes, component)});

    return result;
  }
  
  public ArrayList<XBitSet> get(XBitSet scope, XBitSet neighbors) {
    ArrayList<XBitSet> result = new ArrayList<>();
    for (int nn = 1; nn <= width; nn++) {
      if (root[nn] != null) {
        root[nn].get(scope.unionWith(neighbors).toByteArray(), 
          neighbors.toByteArray(), nn, scope, 
          result);
      }
    }
    if (VERIFY) {
      Set<XBitSet> rSet = new HashSet<>();
      rSet.addAll(result);
      Set<XBitSet> correct = new HashSet<>();
      for (XBitSet component: sieved.keySet()) {
        if (component.isSubset(scope) &&
            neighbors.unionWith(sieved.get(component)).cardinality() <= width) {
          correct.add(component);
        }
      }
      boolean isCorrect = true;
      for (XBitSet component: correct) {
        if (!rSet.contains(component)) {
          isCorrect = false;
          XBitSet sep = g.neighborSet(component);
          System.out.println("missing " + component + ", sep = " + sep);
          System.out.println(" for get(" + scope + ", " + neighbors + ")");
          System.out.println(" union sep = " + sep.unionWith(scope));
          if (saveSieveSeq) {
            System.out.println("sieve sequece is written to file:" + sieveSequencePath);
            try {
              ssStream = new PrintStream(new FileOutputStream(sieveSequencePath));
            } catch (FileNotFoundException e) {
              e.printStackTrace();
            }
            ssStream.println(sieveSequence.size());
            for (XBitSet c: sieveSequence) {
              ssStream.println(c);
            }
            ssStream.close();
          }
//          assert false;

        }
      }
      for (XBitSet component: rSet) {
        if (!correct.contains(component)) {
          isCorrect = false;
          System.out.println("extra " + component + 
              "(" + g.neighborSet(component) + ")" + 
              ", for get(" + scope + ", " + neighbors + ")");
        }
      }
      if (!isCorrect) {
//        dump();
      }
    }
    return result;
  }
  
  void dump() {
    System.out.println("sieve for n = " + n + ", width = " + width);
    for (int nn = 1; nn <= width; nn++) {
      if (root[nn] == null) {
        System.out.println("width " + nn + " sieve empty");
      }
      else {
        System.out.println("width " + nn + ":" );
        root[nn].dump("");
      }
    }
  }
   
  class Node {
    int d;
    NodeType type;
    Object labels;
    Node[] children;
    XBitSet component;
    
    Node(int d, NodeType type, Object labels, Node[] children) {
      this.d = d;
      this.type = type;
      this.labels = labels;
      this.children = children;
    }

    void add(byte[] closureBytes, XBitSet component) {
      switch (type) {
      case BYTE: {
        byte[] bytes = (byte[]) labels;
        byte b = 0;
        if (d < closureBytes.length) {
          b = closureBytes[d];
        }
        int i = Arrays.binarySearch(bytes, b); 
        if (i >= 0) {
          children[i].add(closureBytes, component);
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
          ctmp[i] = newEntry(d + 1, closureBytes, component);
          children = ctmp;
        }
        break;
      }
      case SHORT: {
        short label = 0;
        for (int j = Short.BYTES - 1; j >= 0; j--) {
           label = (short) (0xffff & (label << 8));
           if (d + j < closureBytes.length) { 
             label |= closureBytes[d + j] & 0xff;
           }
        }

        short[] shorts = (short[]) labels;
        int i = Arrays.binarySearch(shorts, label);
        if (i >= 0) {
          children[i].add(closureBytes, component);
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
          ctmp[i] = newEntry(d + Short.BYTES, closureBytes, component);
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
           if (d + j < closureBytes.length) { 
             label |= closureBytes[d + j] & 0xff;
           }
        }
        int[] ints = (int[]) labels;
        int i = Arrays.binarySearch(ints, label);
        if (i >= 0) {
          children[i].add(closureBytes, component);
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
          ctmp[i] = newEntry(d + Integer.BYTES, closureBytes, component);
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
           if (d + j < closureBytes.length) { 
             label |= closureBytes[d + j] & 0xff;
           }
        }
        long[] longs = (long[]) labels;
        int i = Arrays.binarySearch(longs, label);
        if (i >= 0) {
          children[i].add(closureBytes, component);
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
          ctmp[i] = newEntry(d + Long.BYTES, closureBytes, component);
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
    
    void get(byte[] closureBytes, byte[] neighbBytes, int nNeighb, 
        XBitSet scope, ArrayList<XBitSet> result) {
      if (type == NodeType.LEAF) {
        if (component.isSubset(scope)) {
          result.add(component);
        }
        return;
      }
      
      if (type == NodeType.BYTE) {
        byte[] bytes = (byte[]) labels;
        byte cl = 0;
        if (d < closureBytes.length) {
          cl = closureBytes[d];
        }
        byte nb = 0;
        if (d < neighbBytes.length) {
            nb = neighbBytes[d];
        }

        for (int i = 0; i < bytes.length; i++) {
          if (((bytes[i] & ~cl) & 0xff) == 0) {
            int extraNeighbs = (nb & ~bytes[i]) & 0xff;
            int nExtra = Integer.bitCount(extraNeighbs);
            if (nNeighb + nExtra <= width) {
              children[i].get(closureBytes, neighbBytes, nNeighb + nExtra, 
                  scope, result);
            }
          }
        }
        return;
      }
      
      int length = typeLength[type.ordinal()];

      long label = 0;
      long neighb = 0;
      for (int i = length - 1; i >= 0; i--) {
         label = label << 8;
         if (d + i < closureBytes.length) { 
           label |= closureBytes[d + i] & 0xff;
         }
         neighb = neighb << 8;
         if (d + i < neighbBytes.length) { 
           neighb |= neighbBytes[d + i] & 0xff;
         }
      }
      
      switch (type) {
      case SHORT: {
        short cl = (short) (0xffff & label);
        short nb = (short) (0xffff & neighb);
        
        short[] shorts = (short[]) labels;
        for (int i = 0; i < shorts.length; i++) {
          if (((shorts[i] & ~cl) & 0xffff) == 0) {
            int extraNeighbs = (nb & ~shorts[i]) & 0xffff;
            int nExtra = Integer.bitCount(extraNeighbs);
            if (nNeighb + nExtra <= width) {
              children[i].get(closureBytes, neighbBytes, nNeighb + nExtra, 
                  scope, result);
            }
          }
        }
        break;
      }
      case INT: {
        int cl = (int) (0xffffffff & label);
        int nb = (int) (0xffffffff & neighb);
        
        int[] ints = (int[]) labels;
        for (int i = 0; i < ints.length; i++) {
          if ((ints[i] & ~cl) == 0) {
            int extraNeighbs = (nb & ~ints[i]) & 0xffffffff;
            int nExtra = Integer.bitCount(extraNeighbs);
            if (nNeighb + nExtra <= width) {
              children[i].get(closureBytes, neighbBytes, nNeighb + nExtra, 
                  scope, result);
            }
          }
        }
        break;
      }
      case LONG: {
        long[] longs = (long[]) labels;
        for (int i = 0; i < longs.length; i++) {
          if ((longs[i] & ~label) == 0) {
            long extraNeighbs = neighb & ~longs[i];
            int nExtra = Long.bitCount(extraNeighbs);
            if (nNeighb + nExtra <= width) {
              children[i].get(closureBytes, neighbBytes, nNeighb + nExtra, 
                  scope, result);
            }
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
        System.out.println(" " + component);
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
  
  static void debug(String path, String name, int k) {
    /*
missing 7{1, 3, 24, 27, 32, 47, 53}, sep = 28{2, 5, 8, 9, 13, 15, 20, 23, 25, 28, 29, 30, 35, 40, 41, 44, 45, 46, 50, 52, 56, 60, 61, 62, 63, 66, 68, 69}
 for get(8{1, 3, 24, 27, 30, 32, 47, 53}, 28{2, 5, 8, 9, 13, 15, 20, 21, 23, 25, 28, 29, 35, 40, 41, 44, 45, 46, 50, 52, 56, 60, 61, 62, 63, 66, 68, 69})
 union sep = 35{1, 2, 3, 5, 8, 9, 13, 15, 20, 23, 24, 25, 27, 28, 29, 30, 32, 35, 40, 41, 44, 45, 46, 47, 50, 52, 53, 56, 60, 61, 62, 63, 66, 68, 69}
sieve sequece is written to file:sieveSequence 
     */
    Graph g = Graph.readGraph("instance/random", "gnm_070_280_1");
    XBitSet missing = new XBitSet(new int[]
        {1, 3, 24, 27, 32, 47, 53}
        );

    XBitSet scope = new XBitSet(new int[]
        {1, 3, 24, 27, 30, 32, 47, 53}
        );
    XBitSet sep = new XBitSet(new int[]
        {2, 5, 8, 9, 13, 15, 20, 21, 23, 25, 28, 29, 35, 40, 41, 44, 45, 46, 50, 52, 56, 60, 61, 62, 63, 66, 68, 69}
    );
    
    ArrayList<XBitSet> sieveSeq = 
        readXBitSets("sieveSequence");
    SubblockSieve sieve = new SubblockSieve(g, k + 1);
    boolean added = false;
    int i0 = 61638;
    
    for (int i = 0; i < i0; i++) {
      XBitSet c = sieveSeq.get(i);
//      if (c.equals(missing)) {
//        added = true;
//      }
      sieve.add(c, g.neighborSet(c));
//      ArrayList<XBitSet> retrieved = sieve.get(scope, sep);
//      if (added && !retrieved.contains(missing)) {
//        System.out.println(i);
//      }
    }
    ArrayList<XBitSet> retrieved = sieve.get(scope, sep);
    System.out.println("retrieved contains missing: " + retrieved.contains(missing));
    sieve.dump();
    XBitSet c = sieveSeq.get(i0);
    sieve.add(c, g.neighborSet(c));
    System.out.println("added: " + c + ", sep = " + g.neighborSet(c));
    retrieved = sieve.get(scope, sep);
    System.out.println("retrieved contains missing: " + retrieved.contains(missing));
    sieve.dump();
  }
  
  static ArrayList<XBitSet> readXBitSets(String path) {
    ArrayList<XBitSet> result = new ArrayList<>();
    try {
      BufferedReader br = new BufferedReader(new FileReader(path));
      String line = br.readLine();
      int n = Integer.parseInt(line.trim());
      for (int i = 0; i < n; i++) {
        line = br.readLine().trim();
        int p = line.indexOf("{");
        String s = line.substring(0, p);
        int card = Integer.parseInt(s);
        int q = line.indexOf("}");
        String[] t = line.substring(p + 1, q).split(",");
        XBitSet vs = new XBitSet();
        for (String e: t) {
          int v = Integer.parseInt(e.trim());
          vs.set(v);
        }
        result.add(vs);
      }
      br.close();
      return result;
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    return null;
  }

  public static void main(String[] args) {
    debug("instance/random", "gnm_070_280_1", 28);
  }
}