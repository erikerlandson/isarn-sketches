/*
Copyright 2020 Erik Erlandson

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

package org.isarnproject.sketches.java;

import java.lang.System;
import java.lang.StringBuilder;
import java.util.Arrays;
import java.util.Comparator;
import java.io.Serializable;
import java.util.concurrent.ThreadLocalRandom;
import java.util.Random;

public class QCDF implements Serializable {
    protected int K = 0;
    protected double M = 0;
    protected double cmin = Double.NaN;
    protected double cmax = Double.NaN;
    protected double[] cent = null;
    protected double[] mass = null;
    protected boolean discrete = true;

    // cumulative masses
    protected double[] cmss = null;

    public QCDF(final int k) {
        if (k < 2) {
            throw new IllegalArgumentException("number of clusters must be >= 2");
        }
        K = 0;
        M = 0.0;
        cmin = Double.NaN;
        cmax = Double.NaN;
        cent = new double[k];
        mass = new double[k];
        discrete = true;
        cmss = null;
    }

    public void merge(QCDF that) {
        Integer[] indexes = new Integer[that.K];
        for (int j = 0; j < that.K; ++j) indexes[j] = j;
        // sort so that largest clusters are first.
        // inserting large to small yields stable distribution estimations
        Comparator<Integer> cmp = new Comparator<Integer>() {
            @Override
            public int compare(Integer a, Integer b) {
                return (int)Math.signum(that.mass[b] - that.mass[a]);
            }
        };
        Arrays.sort(indexes, cmp);
        for (int j: indexes) update(that.cent[j], that.mass[j]);        
    }

    public final void update(double x) {
        update(x, 1.0);
    }

    public void update(final double x, final double w) {
        if (w <= 0.0) {
            throw new IllegalArgumentException("weight must be > 0");
        }
        // adding new data invalidates any precomputed cumulative mass table
        cmss = null;
        if (K < cent.length) {
            // we still haven't filled all the table entries
            if (K == 0) cmin = cmax = x;
            else {
                cmin = Math.min(cmin, x);
                cmax = Math.max(cmax, x);
            }
            // identify an insertion point
            final int j = Arrays.binarySearch(cent, 0, K, x);
            if (j >= 0) {
                // landed on existing cluster: add its mass and we're done
                M += w;
                mass[j] += w;
            } else {
                // a new x value: insert as a new cluster
                insert(-(j + 1), x, w);
            }
            return;
        }
        // begin logic for an already-full table
        // get the index of the cluster closest to x
        final int j = closest(x);
        if (x == cent[j]) {
            // landed on existing cluster: add its mass and we're done
            M += w;
            mass[j] += w;
            return;
        }
        // we're now entering a non-discrete cluster update
        // so flag that this sketch is no longer reliably tracking discrete values
        discrete = false;
        // check for x landing outside the current cluster boundaries
        if (((j == K-1) && (x > cent[j])) ||
            ((j == 0)   && (x < cent[j]))) {
            // x landed somewhere outside of the cluster boundaries
            if (x > cmax) {
                double xt = cmax;
                cmax = x;
                M += 1.0;
                if (w > 1.0) {
                    double r = Math.max(0.5, (w - 1.0)/w);
                    update(cent[j] + r*(x-cent[j]), w-1.0);
                }
                update(xt, 1.0);
            } else if (x < cmin) {
                double xt = cmin;
                cmin = x;
                M += 1.0;
                if (w > 1.0) {
                    double r = Math.max(0.5, (w - 1.0)/w);
                    update(cent[j] - r*(cent[j]-x), w-1.0);
                }
                update(xt, 1.0);
            } else if ((mass[j] < M / (double)K) || (w < 1.0)) {
                // I need a catch for w<1, and this is reasonable as long as
                // w<1 is uncommon. The only way currently I see that assumption to
                // break is if a user deliberately inserts many points with weight < 1,
                // and also in substantially monotonic order. If that happens I claim the
                // tool isn't being used properly, but worth noting here.
                cluster1(x, w, j);
                M += w;
            } else {
                // Insert a new cluster. So first compact the largest cluster to make room
                compact(j == (K-1));
                cent[j] = x;
                mass[j] = w;
                M += w;
            }
        } else {
            // x landed in the interior
            // in a situation where distribution of incoming points is primarily stationary,
            // this is by far the most common execution path
            if (w > 1.0) {
                // cluster-mode update - allocate cluster's mass to neighbors
                if (x > cent[j]) cluster2(x, w, j, j + 1);
                else             cluster2(x, w, j - 1, j);
                M += w;
            } else {
                // if w is not > 1, w <= 1
                // point-mode update - allocate to nearest cluster
                cluster1(x, w, j);
                M += w;
            }
        }
    }

    protected void cluster1(final double x, final double w, final int j) {
        mass[j] += w;
        cent[j] += (x - cent[j]) / mass[j];        
    }

    protected void cluster2(final double x, final double w, final int j1, final int j2) {
        // assumes j1 < j2, and both are valid indexes into cent & mass arrays
        // the intended use is inserting clusters: where w > 1
        // the mass allocation ratio is derived assuming individual points (w=1)
        // are allocated to nearest cluster.
        double c1 = cent[j1];
        double c2 = cent[j2];
        double r2 = (x - c1) / (c2 - c1);
        double w2 = w * r2;
        double w1 = w - w2;
        double m1 = mass[j1];
        double m2 = mass[j2];
        cent[j1] = (m1*c1 + w1*x)/(m1+w1);
        mass[j1] += w1;
        cent[j2] = (m2*c2 + w2*x)/(m2+w2);
        mass[j2] += w2;
    }

    protected void compact(final boolean left) {
        compact(largest(), left);
    }

    protected void compact(final int jc, final boolean left) {
        if (jc == 0) {
            // merge leftmost into it's neighbor to the right
            cluster1(cent[jc], mass[jc], jc + 1);
        } else if (jc == K-1) {
            // merge rightmost into it's neighbor to the left
            cluster1(cent[jc], mass[jc], jc - 1);
        } else {
            // merge interior to both its neighbors
            cluster2(cent[jc], mass[jc], jc - 1, jc + 2);
        }
        if (left) {
            // compact to the left (free up rightmost slot)
            for (int j = jc + 1; j < K; ++j) {
                cent[j-1] = cent[j];
                mass[j-1] = mass[j];
            }
        } else {
            // compact to the right
            for (int j = jc; j > 0; --j) {
                cent[j] = cent[j-1];
                mass[j] = mass[j-1];
            }
        }
    }

    protected int largest() {
        // identify largest cluster
        int jmax = 0;
        double mmax = mass[0];
        for (int j = 1;  j < K;  ++j) {
            if (mass[j] > mmax) {
                jmax = j;
                mmax = mass[j];
            }
        }
        return jmax;
    }

    protected void insert(final int j, final double x, final double w) {
        int sz = cent.length;
        double[] newCent = cent;
        double[] newMass = mass;
        if (K == sz) {
            int szinc = (int)Math.ceil(0.1 * (double)sz);
            sz += szinc;
            newCent = new double[sz];
            newMass = new double[sz];
            System.arraycopy(cent, 0, newCent, 0, j);
            System.arraycopy(mass, 0, newMass, 0, j);
        }
        // arraycopy can handle when cent == newCent
        System.arraycopy(cent, j, newCent, 1 + j, K - j);
        System.arraycopy(mass, j, newMass, 1 + j, K - j);
        // do this after copies above
        newCent[j] = x;
        newMass[j] = w;
        K += 1;
        cent = newCent;
        mass = newMass;
        M += w;
    }

    protected int closest(final double x) {
        int j = Arrays.binarySearch(cent, 0, K, x);
        // exact match, return its index:
        if (j >= 0) return j;
        // x is not a cluster center, get its insertion index:
        j = -(j + 1);
        // x is to left of left-most cluster:
        if (j == 0) return j;
        // x is to right of right-most cluster:
        if (j == K) return j - 1;
        // x is between two clusters, return index of closest:
        double dL = x - cent[j - 1];
        double dR = cent[j] - x;
        return (dL < dR) ? (j - 1) : j;
    }
}
