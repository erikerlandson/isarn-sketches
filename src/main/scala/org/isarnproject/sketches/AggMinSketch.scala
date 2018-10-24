/*
Copyright 2018 Erik Erlandson

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package org.isarnproject.sketches

import org.isarnproject.algebraAPI.{
  MonoidAPI => Monoid,
  AggregatorAPI => Aggregator
}

trait AggMinSketch[K, D, A] {
  def d: Int  // rows = number of hash functions
  def w: Int  // cols = hash modulus
  def data: Array[Array[A]]
  def hash(j: Int): K => Int

  // aggregator, aka updating monoid - in count-min, this is addition
  def agg: Aggregator[A, D]
  // query monoid - in count-min sketch, this is "minimum"
  def mq: Monoid[A]

  private final def hash(r: Int, k: K): Int = math.abs(hash(r)(k)) % w

  // Agg Min Sketch is an updating monoid, aka aggregator
  def update(k: K, v: D): Unit = {
    (0 until d).foreach { r =>
        val c = hash(r, k)
        data(r)(c) = agg.lff(data(r)(c), v)
    }
  }
  def merge(that: AggMinSketch[K, D, A]): Unit = {
    val dthis = data
    val dthat = that.data
    val am = agg.monoid
    for {
      r <- 0 until d;
      c <- 0 until w
    } {
      dthis(r)(c) = am.combine(dthis(r)(c), dthat(r)(c))
    }
  }

  // generalized count-min query
  def query(k: K): A =
    (0 until d).iterator
      .map { r => data(r)(hash(r, k)) }
      .foldLeft(mq.empty) { case (fa, a) => mq.combine(fa, a) }
}

object AggMinSketch {
  case class NumericMax[N](max: N)

  implicit val intNumericMax = NumericMax[Int](Int.MaxValue)

  def minMonoid[N](implicit num: scala.math.Numeric[N], max: NumericMax[N]) = new Monoid[N] {
    def empty: N = max.max
    def combineAll(as: TraversableOnce[N]): N = as.foldLeft(empty) { case (t, e) => num.min(t, e) }
    def combine(x: N, y: N) = num.min(x, y)
    def combineAllOption(as: TraversableOnce[N]) = if (as.isEmpty) None else Some(combineAll(as))
  }

  def addMonoid[N](implicit num: scala.math.Numeric[N]) = new Monoid[N] {
    def empty: N = num.zero
    def combineAll(as: TraversableOnce[N]): N = as.foldLeft(empty) { case (t, e) => num.plus(t, e) }
    def combine(x: N, y: N) = num.plus(x, y)
    def combineAllOption(as: TraversableOnce[N]) = if (as.isEmpty) None else Some(combineAll(as))
  }

  def addAggregator[N](implicit num: scala.math.Numeric[N]) = new Aggregator[N, N] {
    val monoid = addMonoid[N]
    def lff = (m: N, d: N) => num.plus(m, d)
    def mf = (d: N) => d
    def aggregate(as: TraversableOnce[N]) = as.foldLeft(num.zero) { case (t, e) => num.plus(t, e) }
  }

  type CountMinSketch[K] = AggMinSketch[K, Int, Int]

  def countMinSketch[K](dp: Int, wp: Int) = new CountMinSketch[K] {
    val d = dp
    val w = wp
    val mq = minMonoid[Int]
    val agg = addAggregator[Int]
    val data = Array.fill(d) { Array.fill(w)(0) }
    def hash(j: Int) = (k: K) => scala.util.hashing.MurmurHash3.productHash(new Tuple1(k), (j + 11) * (j + 13))
  }

  def countMinMonoid[K](dp: Int, wp: Int) = new Monoid[CountMinSketch[K]] {
    def empty: CountMinSketch[K] = countMinSketch[K](dp, wp)
    def combine(x: CountMinSketch[K], y: CountMinSketch[K]): CountMinSketch[K] = {
      val r = empty
      r.merge(x)
      r.merge(y)
      r
    }
    def combineAll(as: TraversableOnce[CountMinSketch[K]]) = as.foldLeft(empty) { case (t, e) => combine(t, e) }
    def combineAllOption(as: TraversableOnce[CountMinSketch[K]]) = if (as.isEmpty) None else Some(combineAll(as))
  }

  def countMinAggregator[K](dp: Int, wp: Int) = new Aggregator[CountMinSketch[K], K] {
    val monoid = countMinMonoid[K](dp, wp)
    def lff = (m: CountMinSketch[K], d: K) => { m.update(d, 1); m }
    def mf = (d: K) => { val m = monoid.empty; m.update(d, 1); m }
    def aggregate(as: TraversableOnce[K]) = as.foldLeft(monoid.empty) { case (t, e) => lff(t, e) }
  }

  // There are a bunch of possible heuristic definitions for what min(cms1, cms2) means.
  // 1. pick the one whose sum of matrix elements is smallest (L1 norm over elements)
  // 2. for each row, pick the row from either cms1 or cms2 whose element sum is smallest (L1 of row)
  // 3. if you are willing to generalize what information is available to a query, you could
  // pick the cms whose min-query for a given key is smallest.
  def countMinQueryMonoid[K](dp: Int, wp: Int) = new Monoid[CountMinSketch[K]] {
    def empty: CountMinSketch[K] = {
      val e = countMinSketch[K](dp, wp)
      for { r <- 0 until dp; c <- 0 until wp } {
        e.data(r)(c) = Int.MaxValue
      }
      e
    }
    def combine(x: CountMinSketch[K], y: CountMinSketch[K]):CountMinSketch[K] =
      if (norm(x) < norm(y)) x else y
    def combineAll(as: TraversableOnce[CountMinSketch[K]]) = as.foldLeft(empty) { case (t, e) => combine(t, e) }
    def combineAllOption(as: TraversableOnce[CountMinSketch[K]]) = if (as.isEmpty) None else Some(combineAll(as))
    private def norm(x: CountMinSketch[K]): Long =
      x.data.iterator.map { row => row.iterator.map { _.toLong }.sum }.sum
  }

  def metaSketch[QK, DK](dp: Int, wp: Int) = new AggMinSketch[QK, DK, CountMinSketch[DK]] {
    val d = dp
    val w = wp
    val mq = countMinQueryMonoid[DK](dp, wp)
    val agg = countMinAggregator[DK](dp, wp)
    val data = Array.fill(d) { Array.fill(w) { agg.monoid.empty } }
    def hash(j: Int) = (k: QK) => scala.util.hashing.MurmurHash3.productHash(new Tuple1(k), (j + 11) * (j + 13))
  }

  def innerProduct[K](s1: CountMinSketch[K], s2: CountMinSketch[K]): Long = {
    require(s1.d == s2.d)
    require(s1.w == s2.w)
    def ip(r: Int): Long = {
      val (d1, d2) = (s1.data(r), s2.data(r))
      (0 until s1.w).iterator.map { c => d1(c).toLong * d2(c).toLong }.sum
    }
    (0 until s1.d).iterator.map { ip(_) }.min
  }
}
