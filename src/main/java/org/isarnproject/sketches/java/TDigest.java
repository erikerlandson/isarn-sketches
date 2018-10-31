/*
Copyright 2016 Erik Erlandson

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
import java.util.Arrays;
import java.io.Serializable;

public class TDigest implements Serializable {
    // these need to be private when the dust settles
    public double C = 0.1;
    public int maxDiscrete = 0;
    public int nclusters = 0;
    public double Z = 0.0;
    public double[] cent = null;
    public double[] mass = null;
    public double[] ftre = null;

    public TDigest() {
        // estimate an initial (sz) from compression?
        int sz = 5;
        cent = new double[sz];
        mass = new double[sz];
        ftre = new double[1 + sz];
        // ftre is 1-based. set ftre[0] to zero just to be tidy
        ftre[0] = 0.0;
    }

    public final void update(double x) {
        update(x, 1.0);
    }

    public final void update(double x, double w) {
        if (nclusters == 0) {
            // clusters are empty, so (x,w) becomes the first cluster
            cent[0] = x;
            Z = w;
            mass[0] = w;
            ftre[1] = w;
            nclusters += 1;
            return;
        }
        if (nclusters < maxDiscrete) {
            // we are under the limit for discrete values to track
            int j = Arrays.binarySearch(cent, 0, nclusters, x);
            if (j >= 0) {
                // landed on existing cluster: add its mass and we're done
                Z += w;
                mass[j] += w;
                ftInc(j, w);
            } else {
                // a new x value: insert as a new discrete cluster
                newCluster(-(j + 1), x, w);
            }
            return;
        }
        // get the index of the cluster closest to x
        int j = closest(x);
        if (x == cent[j]) {
            // landed on existing cluster: add its mass and we're done
            Z += w;
            mass[j] += w;
            ftInc(j, w);
            return;
        }
        double m = mass[j];
        // q is the quantile of the closest cluster to x
        // (ftSum does the right thing (return 0) for j = 0)
        double q = (ftSum(j - 1) + (m / 2.0)) / Z;
        // this is the upper-bound for the mass of closest cluster
        double ub = C * Z * q * (1.0 - q);
        // dm is how much mass we're allowed to add to closest cluster
        double dm = Math.min(w, Math.max(0.0, ub - m));
        // rm is the remainder of the mass
        double rm = w - dm;
        // add any allowable mass to closest cluster
        if (dm > 0.0) {
            Z += dm;
            mass[j] += dm;
            ftInc(j, dm);
        }
        // if there is remaining mass, it becomes a new cluster
        if (rm > 0.0) newCluster((x < cent[j]) ? j : j + 1, x, w);
    }

    private final void newCluster(int j, double x, double w) {
        double[] newCent = cent;
        double[] newMass = mass;
        double[] newFtre = ftre;
        int sz = cent.length;
        if (nclusters >= sz) {
            int szinc = (int)Math.ceil(0.1 * (double)sz);
            sz += szinc;
            newCent = new double[sz];
            newMass = new double[sz];
            newFtre = new double[1 + sz];
            System.arraycopy(cent, 0, newCent, 0, j);
            System.arraycopy(mass, 0, newMass, 0, j);
        }
        // arraycopy can handle when cent == newCent
        System.arraycopy(cent, j, newCent, 1 + j, nclusters - j);
        System.arraycopy(mass, j, newMass, 1 + j, nclusters - j);
        // do this after copies above
        newCent[j] = x;
        newMass[j] = w;
        nclusters += 1;
        cent = newCent;
        mass = newMass;
        ftre = newFtre;
        Arrays.fill(ftre, 0, 1 + nclusters, 0.0);
        for (int k = 0; k < nclusters; ++k) ftInc(k, mass[k]);
        Z += w;
    }

    private final int closest(double x) {
        int j = Arrays.binarySearch(cent, 0, nclusters, x);
        // exact match, return its index:
        if (j >= 0) return j;
        // x is not a cluster center, get its insertion index:
        j = -(j + 1);
        // x is to left of left-most cluster:
        if (j == 0) return j;
        // x is to right of right-most cluster:
        if (j == nclusters) return j - 1;
        // x is between two clusters, return index of closest:
        double dL = x - cent[j - 1];
        double dR = cent[j] - x;
        return (dL < dR) ? (j - 1) : j;
    }

    // cumulative-sum algorithm for a Fenwick tree
    private final double ftSum(int j) {
        j += 1;
        double s = 0.0;
        while (j > 0) {
            s += ftre[j];
            j -= j & (-j); // dec by least significant nonzero bit of j
        }
        return s;
    }

    // increment algorithm for a Fenwick tree
    private final void ftInc(int j, double w) {
        j += 1;
        while (j <= nclusters) {
            ftre[j] += w;
            j += j & (-j); // inc by least significant nonzero bit of j
        }
    }
}
