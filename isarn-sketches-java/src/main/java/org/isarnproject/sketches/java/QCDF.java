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
    protected double cmin = Double.POSITIVE_INFINITY;
    protected double cmax = Double.NEGATIVE_INFINITY;
    protected double[] cent = null;
    protected double[] mass = null;
    protected boolean discrete = true;

    // cumulative masses
    protected double[] cmss = null;
    int reclusters = 0;

    public int nrc() { return reclusters; }
    
    public QCDF(final int k) {
        if (k < 2) {
            throw new IllegalArgumentException("number of clusters must be >= 2");
        }
        K = 0;
        M = 0.0;
        cmin = Double.POSITIVE_INFINITY;
        cmax = Double.NEGATIVE_INFINITY;
        cent = new double[k];
        mass = new double[k];
        discrete = true;
        cmss = null;
        reclusters = 0;
    }

    public void merge(QCDF that) {
        // Merging min/max first so invariants are respected during
        // subsequent merging logic
        cmin = Math.min(cmin, that.cmin);
        cmax = Math.max(cmax, that.cmax);
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

    public final void update(final double x) {
        update(x, 1.0);
    }

    public final void update(final double[] data) {
        for (double x: data) update(x, 1.0);
    }

    public void update(final double x, final double w) {
        if (w <= 0.0) throw new IllegalArgumentException("weight must be > 0");
        // adding new data invalidates any precomputed cumulative mass table
        cmss = null;
        // maintain global max and min values
        cmin = Math.min(cmin, x);
        cmax = Math.max(cmax, x);
        if (K < cent.length) {
            // cluster elements are not fully populated yet 
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
        } else {
            // begin logic for an already-full table
            // get the index of the cluster closest to x
            final int j = closest(x);
            if (x == cent[j]) {
                // landed on existing cluster: add its mass and we're done
                M += w;
                mass[j] += w;
            } else {
                // we're now entering a non-discrete cluster update
                // so flag that this sketch is no longer reliably tracking discrete values
                discrete = false;
                // update nearest cluster with (x,w)
                M += w;
                if (ddnewclust(x, w, j)) {
                    // j is 0 or K-1 and we have made room for a new cluster, in response
                    // to heuristically detecting possible data drift to left or right
                    mass[j] = w;
                    cent[j] = x;
                } else {
                    // otherwise we add to nearest cluster normally
                    mass[j] += w;
                    cent[j] += (x - cent[j]) / mass[j];
                }
            }
        }
    }

    protected boolean ddnewclust(final double x, final double w, final int j) {
        if (((j == 0) && (x < cent[j]) || (j == K-1) && (x > cent[j])) &&
            ((w + mass[j]) > (M / (double)K))) {
            reclusters += 1;
            // heuristic indicates likely non-stationary movement to left or right
            // look at the smallest cluster
            int jmrg = ncsmallest();
            // if the smallest cluster is < M/(100*K) then merge that, otherwise
            // identify a cluster with the closest neighbor (the smaller of the pair)
            if (mass[jmrg] >= (M / (100.0 * K))) jmrg = closestsmaller();
            // merge our choice to its closest neighbor
            final int jnbr = ncclosest(jmrg);
            mass[jnbr] += mass[jmrg];
            cent[jnbr] += (cent[jmrg] - cent[jnbr]) / mass[jnbr];
            // shift left or right to make room at the correct end for a new cluster
            if (j == 0) {
                for (int k = jmrg; k > 0; --k) {
                    mass[k] = mass[k-1];
                    cent[k] = cent[k-1];
                }
            } else {
                for (int k = jmrg; k < K-1; ++k) {
                    mass[k] = mass[k+1];
                    cent[k] = cent[k+1];
                }
            }
            return true;
        }
        return false;
    }

    // find closest pair, and return index of the smaller one
    protected int closestsmaller() {
        int jmin = 0;
        double dmin = Double.POSITIVE_INFINITY;
        for (int j = 0; j < K-1; ++j) {
            if (dmin > (cent[j+1] - cent[j])) {
                dmin = cent[j+1] - cent[j];
                jmin = (mass[j] < mass[j+1]) ? j : j+1;
            }
        }
        return jmin;        
    }

    protected int ncsmallest() {
        int jmin = 0;
        double dmin = mass[0];
        for (int j = 1; j < K; ++j) {
            if (dmin > mass[j]) {
                dmin = mass[j];
                jmin = j;
            }
        }
        return jmin;        
    }

    // given j, return index of cluster-j's closest neighbor
    protected int ncclosest(final int j) {
        if (j == 0) return j + 1;
        if (j == K-1) return K-2;
        double dL = cent[j] - cent[j-1];
        double dR = cent[j+1] - cent[j];
        return (dL < dR) ? (j-1) : (j+1);
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

    public final void executeBinarySearch(final double[] data) {
        for (double x: data) Arrays.binarySearch(cent, 0, K, x);
    }

    public int closest(final double x) {
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

    public double cdfCont(final double x) {
        if (K == 0) return Double.NaN;
        // the following also gives best-effort for K = 1
        if (x < cmin) return 0.0;
        if (x >= cmax) return 1.0;
        // if we get here K >= 2
        // why? because cmin <= x < cmax => cmin < cmax
        fillcmss();
        // cent[j] <= x < cent[j+1]
        final int j = rcovj(x);
        double c1 = (j >= 0) ? cent[j] : cmin;
        double c2 = (j < K-1) ? cent[j+1] : cmax;
        double m0 = ((j > 0) ? cmss[j-1] : 0.0) + ((j >= 0) ? mass[j] / 2.0 : 0.0);
        double m1 = (j >= 0) ? mass[j] / 2.0 : 0.0;
        double m2 = (j < K-1) ? mass[j+1] / 2.0 : 0.0;
        if (j == 0 && cmin == cent[0]) {
            m0 = 0.0;
            m1 = mass[0];
        }
        if (j == K-2 && cmax == cent[K-1]) {
            m2 = mass[K-1];
        }
        return (m0 + ((m1 + m2) * (x - c1) / (c2 - c1))) / M;
    }

    protected void fillcmss() {
        // requires cmss to be nulled out whenever the underlying
        // clusters change due to updating with new data
        if (cmss != null) return;
        cmss = new double[K];
        double s = 0;
        for (int j = 0; j < K; ++j) {
            s += mass[j];
            cmss[j] = s;
        }
    }

    // returns the left index of a right-cover
    // cent[j] <= x < cent[j+1]
    protected int rcovj(final double x) {
        int j = Arrays.binarySearch(cent, 0, K, x);
        // exact match, return its index:
        if (j >= 0) return j;
        // x is not a cluster center, get its insertion index:
        j = -(j + 1);
        // return the index to the left of x:
        return j - 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("QCDF(");
        sb.append(K).append(", ");
        sb.append(M).append(", ");
        sb.append(cmin).append(", ");
        sb.append(cmax).append(", ");
        sb.append(discrete).append(", ");
        sb.append("[");
        for (int j = 0; j < K; ++j) {
            if (j > 10) {
                sb.append(" ...");
                break;
            }
            if (j > 0) sb.append(", ");
            sb.append(cent[j])
                .append(":")
                .append(mass[j]);
        }
        sb.append("]");
        sb.append(")");
        return sb.toString();        
    }
}
