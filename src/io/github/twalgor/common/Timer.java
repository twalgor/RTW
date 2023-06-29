package io.github.twalgor.common;

public class Timer {
  private int interval;
  private long t0;
  private long tExpire;
  private long tCumulative;
  private boolean running;
  
  public Timer(int interval) {
    this.interval = interval;
  }
  
  public void start() {
    if (running) {
      throw new RuntimeException("timer started while running");
    }
    t0 = System.currentTimeMillis();
    tExpire = t0 + interval;
    running = true;
  }
  
  public void stop() {
    if (!running) {
      throw new RuntimeException("timer stopped while not running");
    }
    long t = System.currentTimeMillis();
    tCumulative += (t - t0);
    running = false;
  }
  
  public boolean isRunning() {
    return running;
  }
  
  public boolean expired() {
    long t = System.currentTimeMillis();
    return t > tExpire;
  }
  
  public long cumulativeTime() {
    if (!running) {
      return tCumulative;
    }
    else {
      long t = System.currentTimeMillis();
      return tCumulative + (t - t0);
    }
  }
  
}
