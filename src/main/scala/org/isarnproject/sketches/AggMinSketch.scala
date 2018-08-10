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

  // Agg Min Sketch is an updating monoid, aka aggregator
  def update(kv: (K, D)): Unit = {
    val (k, v) = kv
    (0 until d).foreach { r =>
        val c = hash(r)(k) % w
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
      .map { r => data(r)(hash(r)(k) % w) }
      .foldLeft(mq.empty) { case (fa, a) => mq.combine(fa, a) }
}

object AggMinSketch {
/*
  def countMinSketch[K](d: Int, w: Int) = new AggMinSketch[K, Int, Int] {
    val d = d
    val w = w
    def hash(j: Int) = (k: K) => scala.util.hashing.MurmurHash3.productHash(new Tuple1(k), j)
    val mq = new MinimumMonoid[Int]
    val agg = new Aggregator(new AdditionMonoid[Int])
  }
*/
}
