package io.github.twalgor.common;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import io.github.twalgor.decomposer.SemiPID;

public class TreeWidthCertificate {
  Graph g;
  TreeDecomposition td;
  Minor obs;
  
  public TreeWidthCertificate(Graph g, TreeDecomposition td, Minor obs) {
    this.g = g;
    this.td = td;
    this.obs = obs;
  }
  
  public void verify() {
    td.validate();
    int w = widthOf(obs.getGraph());
    if (w == td.width) {
      System.out.println("width " + td.width + " certified by the obstruction");
    }
    else {
      System.out.println("invalid obstruction with width " + w + " for the claimed width " + td.width);
    }
  }
  
  int widthOf(Graph g) {
    return SemiPID.decompose(g).width;
  }

  public static TreeWidthCertificate readCertificate(String path, String name) {
    File certDir = new File(path);
    File certFile = new File(certDir, name + ".twc");
    if (!certFile.exists()) {
      System.out.println("certificate file " + path + " " + name + " does not exist");
      return null;
    }
    BufferedReader br = null;
    try {
      br = new BufferedReader(new FileReader(certFile));
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    }
    try {
      String line = br.readLine();
      System.out.println(line);
      while (!line.startsWith("c treewidth certificate")) {
        line = br.readLine();
        System.out.println(line);
      }
      String[] s = line.split(" ");
      String graphPath = getProperty(s, "graphpath");
      assert graphPath != null;
      File graphFile = new File(graphPath);
      assert graphFile.getName().equals(name + ".gr");
      
      System.out.println("reading graph from " + graphPath);
      Graph g = Graph.readGraph(new File(graphPath));
      System.out.println("graph " + name + " " + g.n + ", " + g.numberOfEdges());

      while (!line.startsWith("c width ")) {
        line = br.readLine();
        System.out.println(line);
      }
      s = line.trim().split(" ");
      String widthString = getProperty(s, "width");
      int width = Integer.parseInt(widthString);

      line = br.readLine();
      System.out.println(line);
      while (line != null && !line.startsWith("s nbags ")) {
        line = br.readLine();
        System.out.println(line);
      }
      if (line == null) {
        return null;
      }
      s = line.trim().split(" ");
      String nbString = getProperty(s, "nbags");
      int nb = Integer.parseInt(nbString);

      TreeDecomposition td = new TreeDecomposition(0, width, g);

      for (int i = 0; i < nb; i++) {
        line = br.readLine();
        System.out.println(line);
        s = line.trim().split(" ");
        assert s[0].equals("b");
        int b = Integer.parseInt(s[1]);
        int[] bag = new int[s.length - 2];
        for (int j = 0; j < s.length - 2; j++) {
          bag[j] = Integer.parseInt(s[j + 2]) - 1; 
        }
        int b1 = td.addBag(bag);
        assert b1 == b;
      }
      for (int i = 0; i < nb - 1; i++) {
        line = br.readLine();
        System.out.println(line);
        s = line.trim().split(" ");
        int b1 = Integer.parseInt(s[0]);
        int b2 = Integer.parseInt(s[1]);
        td.addEdge(b1, b2);
      }

      line = br.readLine();
      System.out.println(line);
      while (line != null && !line.startsWith("s ncomponents ")) {
        line = br.readLine();
        System.out.println(line);
      }
      if (line == null) {
        return null;
      }
      s = line.trim().split(" ");
      String ncString = getProperty(s, "ncomponents");
      int nc = Integer.parseInt(ncString);

      XBitSet[] components = new XBitSet[nc];
      
      for (int i = 0; i < nc; i++) {
        line = br.readLine();
        System.out.println(line);
        s = line.trim().split(" ");
        assert Integer.parseInt(s[0]) == i + 1;
        XBitSet compo = new XBitSet();
        for (int j = 1; j < s.length; j++) {
          compo.set(Integer.parseInt(s[j]) - 1);
        }
        components[i] = compo;
      }

      Minor minor = new Minor(g, components);
      
      return new TreeWidthCertificate(g, td, minor);

    } catch (IOException e) {
      e.printStackTrace();
      return null;
    }
  }

  static String getProperty(String[] s, String key) {
    int i = 0;
    while (i < s.length && !s[i].equals(key)) {
      i++;
    }
    if (i == s.length - 1) {
      return null;
    }
    return s[i + 1];
  }
  
  public static void main(String[] args) {
    String path = "twcert/PACE2017bonus";
    String name = "Promedus_38_15";
    TreeWidthCertificate twc = readCertificate(path, name);
    twc.verify();
  }
}
