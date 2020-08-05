/*
Copyright 2016-2020 Erik Erlandson

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
import java.io.FileWriter;
import java.io.PrintWriter;

/**
 * A t-digest sketch of sampled numeric data
 * <pre>
 * Computing Extremely Accurate Quantiles Using t-Digests,
 * Ted Dunning and Otmar Ertl,
 * https://github.com/tdunning/t-digest/blob/master/docs/t-digest-paper/histo.pdf
 * </pre>
 *
 * <pre>
 * import org.isarnproject.sketches.java.TDigest;
 * double[] data = // data that you would like to sketch
 * TDigest sketch = TDigest.sketch(data)
 * // the cumulative distribution function of the sketch; cdf(x) at x = 0
 * double cdf = sketch.cdf(0.0)
 * // inverse of the CDF, evaluated at q = 0.5
 * double cdfi = sketch.cdfInverse(0.5)
 * </pre>
 */
public class TDigest implements Serializable {
    /** maximum number of clusters to use for this sketch */
    protected final int maxClusters;
    /** maximum number of unique discrete values to track */
    protected final int maxDiscrete;

    /** compression (delta in original paper) */
    protected double C = 1.0;
    /** current number of clusters */
    protected int nclusters = 0;
    /** total mass of data sampled so far */
    protected double M = 0.0;
    /** cluster centers */
    protected double[] cent = null;
    /** cluster masses */
    protected double[] mass = null;
    /** cumulative cluster masses, represented as a Fenwick Tree */
    protected double[] ftre = null;

    int nnc = 0;
    int nrc = 0;

    public void dump() {
            /*
        PrintWriter f =  new PrintWriter(new FileWriter("/tmp/stats.txt", true));        
        f.printf("nnc= %d  nrc= %d\n", nnc, nrc);
        f.close();
            */
        System.out.format("nnc= %d  nrc= %d  C= %f  nc= %d\n", nnc, nrc, C, nclusters);
    }

    /** A new t-digest sketching structure with default max-size and maximum discrete tracking. */
    public TDigest() {
        this(MAX_SIZE_DEFAULT, 0, INIT_SIZE_DEFAULT);
    }

    /** Construct a t-digest with the given max-size.
     * Maximum discrete tracking defaults to zero.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     */
    public TDigest(int maxSize) {
        this(maxSize, 0, INIT_SIZE_DEFAULT);
    }

    /** Construct a t-digest with the given maxsize and maximum discrete tracking.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDiscrete maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     */
    public TDigest(int maxSize, int maxDiscrete) {
        this(maxSize, maxDiscrete, INIT_SIZE_DEFAULT);
    }

    /** Construct a t-digest with the given maxsize and maximum discrete tracking.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDisc maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     * @param sz initial capacity to use for internal arrays. Must be &gt; 0.
     */
    public TDigest(int maxSize, int maxDisc, int sz) {
        assert maxSize > 0;
        assert maxDisc >= 0;
        assert maxDisc <= maxSize;
        assert sz > 0;
        this.maxClusters = maxSize;
        this.maxDiscrete = maxDisc;
        // compression such that middle half of (c)(q)(1-q) curve >= 2
        // that is: we can form "2-clusters" from the start, between quantile 0.25 - 0.75
        C = Math.min(3.0, 50.0 / (double)maxSize);
        sz = Math.min(sz, maxSize);
        cent = new double[sz];
        mass = new double[sz];
        ftre = new double[1 + sz];
        // ftre is 1-based. set ftre[0] to zero just to be tidy
        ftre[0] = 0.0;        
    }

    /**
     * Construct a t-digest from a list of cluster centers and masses.
     * Object ser/de is one of the intended use cases for this constructor.
     * NOTE: This constructor assumes the 'cnt' and 'mss' arrays will be owned
     * by the new t-digest object. If 'cnt' and 'mss' are both null then an empty cluster
     * will be created.
     * @param maxClust sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDisc maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in continuous mode.
     * @param comp the initial compression setting
     * @param cnt the list of cluster centers. Assumed to be in sorted order.
     * This array is assumed to be owned by the t-digest object after construction.
     * @param mss a list of cluster masses. Assumed to be parallel to centers.
     * This array is assumed to be owned by the t-digest object after construction.
     */
    public TDigest(int maxClust, int maxDisc, double comp, double cnt[], double mss[]) {
        assert maxClust > 0;
        assert maxDisc >= 0;
        assert maxDisc <= maxClust;
        assert comp > 0.0;
        this.maxClusters = maxClust;
        this.maxDiscrete = maxDisc;
        this.C = comp;
        assert (cnt != null && mss != null) || (cnt == null && mss == null);
        nclusters = (cnt != null) ? cnt.length : 0;
        assert nclusters <= maxClust;
        int sz = nclusters;
        if (sz == 0) {
            // cent, mass and ftre cannot be zero length
            sz = Math.min(maxClust, INIT_SIZE_DEFAULT);
            this.cent = new double[sz];
            this.mass = new double[sz];
        } else {
            this.cent = cnt;
            this.mass = mss;
        }
        assert cent != null && mass != null;
        assert cent.length == sz;
        assert cent.length == mass.length;
        assert cent.length > 0;
        this.ftre = new double[1 + sz];
        Arrays.fill(ftre, 0, 1 + nclusters, 0.0);
        this.M = 0.0;
        for (int j = 0; j < nclusters; ++j) {
            M += mass[j];
            ftInc(j, mass[j]);
        }
    }

    /** Construct a deep copy of another t-digest */
    public TDigest(TDigest that) {
        maxDiscrete = that.maxDiscrete;
        maxClusters = that.maxClusters;
        C = that.C;
        nclusters = that.nclusters;
        M = that.M;
        cent = Arrays.copyOf(that.cent, nclusters);
        mass = Arrays.copyOf(that.mass, nclusters);
        ftre = Arrays.copyOf(that.ftre, 1+nclusters);
    }

    /** Update the sketch with a new sampled value
     * @param x the new sampled value
     */
    public final void update(final double x) {
        update(x, 1.0);
    }

    /** Update the sketch with a new sampled value
     * @param x the new sampled value
     * @param w the weight (aka mass) associated with x
     */
    public final void update(final double x, final double w) {
        if (nclusters <= Math.max((int)(maxClusters * 0.67), maxDiscrete)) {
            // we are under the limit for discrete values to track
            int j = Arrays.binarySearch(cent, 0, nclusters, x);
            if (j >= 0) {
                // landed on existing cluster: add its mass and we're done
                M += w;
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
            M += w;
            mass[j] += w;
            ftInc(j, w);
            return;
        }
        double m = mass[j];
        // q is the quantile of the closest cluster to x
        // (ftSum does the right thing (return 0) for j = 0)
        double q = (ftSum(j - 1) + (m / 2.0)) / M;
        // this is the upper-bound for the mass of closest cluster
        double ub = C * M * q * (1.0 - q);
        // dm is how much mass we're allowed to add to closest cluster
        double dm = Math.min(w, Math.max(0.0, ub - m));
        // rm is the remainder of the mass
        double rm = w - dm;
        if ((rm > 0.0) && (nclusters >= maxClusters)) {
            // if there is remainder, then we will be adding a cluster.
            // if we are also already at maximum clusters, then we need to recluster
            // to make room and then re-insert
            recluster();
            update(x, w);
            return;
        }
        // otherwise we insert the new mass normally
        if (dm > 0.0) {
            // Add any allowable mass to closest cluster and update its center.
            // It is safe to update center this way because it will remain
            // between x and original center, and so cannot move out of its original
            // ordering relative to its neighbors, because x is by previous logic
            // closer to cent[j] than any other cluster.
            double dc = dm * (x - cent[j]) / (m + dm);
            cent[j] += dc;
            M += dm;
            mass[j] += dm;
            ftInc(j, dm);
        }
        // if there is remaining mass, it becomes a new cluster
        if (rm > 0.0) {
            newCluster((x < cent[j]) ? j : j + 1, x, rm);
                //C *= 1.01;
        }
        C *= 0.99999;
    }

    /** Merge another t-digest into this one.
     * @param that the t-digest to merge. This t-digest is unaltered.
     */
    public final void merge(TDigest that) {
        Integer[] indexes = weightedOrdering(that.nclusters, that.cent, that.mass);
        int split = (int)(0.75 * (double)(that.nclusters));
        for (int j = 0; j <= split; ++j) {
            // start by inserting larger or more central clusters first: "middle out"
            update(that.cent[indexes[j]], that.mass[indexes[j]]);
        }
        for (int j = that.nclusters-1; j > split; --j) {
            // finish by inserting clusters out on the tails outward-in:
            // preserves the tail resolution and avoids the pathological
            // scenario where points keep getting added to the end
            update(that.cent[indexes[j]], that.mass[indexes[j]]);
        }
    }

    /** Re-cluster this t-digest by reinserting its clusters. */
    public final void recluster() {
        // This method will iterate until it obtains a clustering that is < maxClusters
        // Actually requiring more than one try should be rare
        nrc += 1;
        if (nclusters < 2) return;
        int sz = cent.length;
        double[] oldCent = cent;
        double[] oldMass = mass;
        cent = new double[sz];
        mass = new double[sz];
        Integer[] indexes = weightedOrdering(nclusters, oldCent, oldMass);
        int iter = 0;
        int nc = nclusters;
        while (true) {
            // reset cluster state to empty
            reset();
             C *= 1.1;
             int split = (int)(0.5 * (double)(nc));
            // we stop short of adding maxClusters, and this prevents recluster from
            // being called recursively during the following updates, which
            // guarantees this will halt
            for (int j = 0; (j <= split) && (nclusters < maxClusters); ++j) {
                // start by inserting larger or more central clusters first: "middle out"
                update(oldCent[indexes[j]], oldMass[indexes[j]]);
            }
            for (int j = nc-1; (j > split) && (nclusters < maxClusters); --j) {
                // finish by inserting clusters out on the tails outward-in:
                // preserves the tail resolution and avoids the pathological
                // scenario where points keep getting added to the end
                update(oldCent[indexes[j]], oldMass[indexes[j]]);
            }
            // if the new clustering size is < maxClusters we declare victory
            iter += 1;
            if (nclusters < maxClusters) break;
            // otherwise we increase the compression and try again
                //System.out.format("C= %f\n", C);
        }
            //if (iter > 1) System.err.format("iter= %d  nclusters=%d\n\n", iter, nclusters);
    }

    /** Reset this t-digest to an empty state */
    public final void reset() {
        nclusters = 0;
        M = 0.0;
    }

    private final Integer[] weightedOrdering(final int n, double[] icent, double[] imass) {
        assert n >= 0;
        assert n <= imass.length;
        assert imass.length == icent.length;
        Integer[] indexes = new Integer[n];
        double z = 0.0;
        for (int j = 0; j < n; ++j) {
            z += imass[j];
            indexes[j] = j;
        }
        // if there is no sorting needed, quit here
        if (n < 2) return indexes;
        double[] weight = new double[n];
        double macc = 0.0;
        for (int j = 0; j < n; ++j) {
            double m = imass[j];
            double q = (macc + (m / 2.0)) / z;
            weight[j] = m * q * (1.0 - q);
            macc += m;
        }
        Comparator<Integer> cmp = new Comparator<Integer>() {
            @Override
            public int compare(Integer a, Integer b) {
                return (int)Math.signum(weight[b] - weight[a]);
            }
        };
        Arrays.sort(indexes, cmp);
        return indexes;
    }

    private final void newCluster(int j, double x, double w) {
        nnc += 1;
        // this method will allocate new memory if necessary but assumes that
        // it is not up against the max-cluster bound
        assert nclusters < maxClusters;
        double[] newCent = cent;
        double[] newMass = mass;
        double[] newFtre = ftre;
        int sz = cent.length;
        if (nclusters >= sz) {
            int szinc = (int)Math.ceil(0.1 * (double)sz);
            sz += szinc;
            sz = Math.min(sz, maxClusters);
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
        M += w;
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

    /** Obtain the number of clusters in this t-digest 
     * @return the number of clusters in this t-digest
     */
    public final int size() {
        return nclusters;
    }

    /** Obtain the total mass sampled by this t-digest
     * @return the total mass
     */
    public final double mass() {
        return M;
    }

    /** Obtain the compression factor for this t-digest
     * @return the current compression factor
     */
    public final double compression() {
        return C;
    }

    /** Obtain the maxsize setting for this t-digest
     * @return the maxsize setting
     */
    public final int getMaxSize() {
        return maxClusters;
    }

    /** Obtain the maximum discrete setting for this t-digest
     * @return the maximum discrete setting
     */
    public final int getMaxDiscrete() {
        return maxDiscrete;
    }

    /** Obtain a reference to this t-digest's cluster center array.
     * NOTE: this array is not safe to modify, and should be used only in "read-only" mode!
     * @return a reference to the cluster center array
     */
    public final double[] getCentUnsafe() {
        return cent;
    }

    /** Obtain a reference to this t-digest's cluster mass array.
     * NOTE: this array is not safe to modify, and should be used only in "read-only" mode!
     * @return a reference to the cluster mass array
     */
    public final double[] getMassUnsafe() {
        return mass;
    }

    /** Obtain a reference to this t-digest's cumulative mass array.
     * This array stores the cumulative masses of clusters in Fenwick Tree format.
     * NOTE: this array is not safe to modify, and should be used only in "read-only" mode!
     * @return a reference to the cumulative mass array
     */
    public final double[] getFTUnsafe() {
        return ftre;
    }

    /** Returns true if this t-digest is empty, false otherwise. */
    public final boolean isEmpty() {
        return nclusters == 0;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("TDigest(");
        for (int j = 0; j < nclusters; ++j) {
            if (j > 25) {
                sb.append(" ...");
                break;
            }
            if (j > 0) sb.append(", ");
            sb.append(cent[j])
                .append(" -> (")
                .append(mass[j])
                .append(", ")
                .append(ftSum(j))
                .append(")");
        }
        sb.append(")");
        return sb.toString();
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest, in
     * "probability density" mode.
     * @return A random number sampled from the sketched distribution
     */
    public final double samplePDF() {
        return samplePDF(ThreadLocalRandom.current());
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest, in
     * "probability density" mode.
     * @param prng a (pseudo) random number generator to use for the random sampling
     * @return A random number sampled from the sketched distribution
     */
    public final double samplePDF(Random prng) {
        return cdfInverse(prng.nextDouble());
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest, in
     * "probability mass" (i.e. discrete) mode.
     * @return A random number sampled from the sketched distribution
     */
    public final double samplePMF() {
        return samplePMF(ThreadLocalRandom.current());
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest, in
     * "probability mass" (i.e. discrete) mode.
     * @param prng a (pseudo) random number generator to use for the random sampling
     * @return A random number sampled from the sketched distribution
     */
    public final double samplePMF(Random prng) {
        return cdfDiscreteInverse(prng.nextDouble());
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest,
     * using "discrete" (PMF) mode if the number of clusters &le; maxDiscrete setting,
     * and "density" (PDF) mode otherwise.
     * @return A random number sampled from the sketched distribution
     */
    public final double sample() {
        return sample(ThreadLocalRandom.current());
    }

    /**
     * Perform a random sampling from the distribution as sketched by this t-digest,
     * using "discrete" (PMF) mode if the number of clusters &le; maxDiscrete setting,
     * and "density" (PDF) mode otherwise.
     * @param prng a (pseudo) random number generator to use for the random sampling
     * @return A random number sampled from the sketched distribution
     */
    public final double sample(Random prng) {
        if (nclusters <= maxDiscrete) {
            return cdfDiscreteInverse(prng.nextDouble());
        } else {
            return cdfInverse(prng.nextDouble());
        }    
    }

    /**
     * Compute a cumulative probability (CDF) for a numeric value, from the estimated probability
     * distribution represented by this t-digest sketch.
     * @param x a numeric value
     * @return the cumulative probability that a random sample from the distribution is &le; x
     */
    public final double cdf(double x) {
        int j1 = rcovj(x);
        if (j1 < 0) return 0.0;
        if (j1 >= nclusters - 1) return 1.0;
        int j2 = j1 + 1;
        double c1 = cent[j1];
        double c2 = cent[j2];
        double tm1 = mass[j1];
        double tm2 = mass[j2];
        double s = ftSum(j1 - 1);
        double d1 = (j1 == 0) ? 0.0 : tm1 / 2.0;
        double m1 = s + d1;
        double m2 = m1 + (tm1 - d1) + ((j2 == nclusters - 1) ? tm2 : tm2 / 2.0);
        double m = m1 + (x - c1) * (m2 - m1) / (c2 - c1);
        return Math.min(m2, Math.max(m1, m)) / M;
    }

    /**
     * Compute a cumulative probability (CDF) for a numeric value, from the estimated probability
     * distribution represented by this t-digest sketch, assuming sketch is "discrete"
     * (e.g. if number of clusters &le; maxDiscrete setting)
     * @param x a numeric value
     * @return the cumulative probability that a random sample from the distribution is &le; x
     */
    public final double cdfDiscrete(double x) {
        int j = rcovj(x);
        return ftSum(j) / M;
    }

    /**
     * Compute the inverse cumulative probability (inverse-CDF) for a quantile value, from the
     * estimated probability distribution represented by this t-digest sketch.
     * @param q a quantile value.  The value of q is expected to be on interval [0, 1]
     * @return the value x such that cdf(x) = q
     */
    public final double cdfInverse(double q) {
        if (q < 0.0 || q > 1.0) return Double.NaN;
        if (nclusters == 0) return Double.NaN;
        if (nclusters == 1) return cent[0];
        double m = q * M;
        int j1 = rmcovj(m);
        int j2 = j1 + 1;
        double c1 = cent[j1];
        double c2 = cent[j2];
        double tm1 = mass[j1];
        double tm2 = mass[j2];
        double s = ftSum(j1 - 1);
        double d1 = (j1 == 0) ? 0.0 : tm1 / 2.0;
        double m1 = s + d1;
        double m2 = m1 + (tm1 - d1) + ((j2 == nclusters - 1) ? tm2 : tm2 / 2.0);
        double x = c1 + (m - m1) * (c2 - c1) / (m2 - m1);
        return Math.min(c2, Math.max(c1, x));
    }

    /**
     * Compute the inverse cumulative probability (inverse-CDF) for a quantile value, from the
     * estimated probability distribution represented by this t-digest sketch,
     * assuming the sketch is "discrete" (e.g. if number of clusters &le; maxDiscrete setting)
     * @param q a quantile value.  The value of q is expected to be on interval [0, 1]
     * @return the smallest value x such that q &le; cdf(x)
     */
    public final double cdfDiscreteInverse(double q) {
        if (q < 0.0 || q > 1.0) return Double.NaN;
        if (nclusters == 0) return Double.NaN;
        if (nclusters == 1) return cent[0];
        double m = q * M;
        int j = lmcovj(m);
        return cent[j];
    }

    // returns the index of a right mass cover
    // ftSum(j) <= m < ftSum(j+1)
    private final int rmcovj(double m) {
        assert nclusters >= 2;
        assert (m >= 0.0) && (m <= M);
        int beg = 0;
        double mbeg = 0.0;
        int end = nclusters - 1;
        double mend = M;
        while ((end - beg) > 1) {
            int mid = (beg + end) / 2;
            double mmid = ftSum(mid);
            if (m >= mmid) {
                beg = mid;
                mbeg = mmid;
            } else {
                end = mid;
                mend = mmid;
            }
        }
        return beg;
    }

    // returns the index of a left mass cover
    // ftSum(j-1) < m <= ftSum(j)
    private final int lmcovj(double m) {
        assert nclusters >= 2;
        assert (m >= 0.0) && (m <= M);
        int beg = -1;
        double mbeg = 0.0;
        int end = nclusters - 1;
        double mend = M;
        while ((end - beg) > 1) {
            int mid = (beg + end) / 2;
            double mmid = ftSum(mid);
            if (m <= mmid) {
                end = mid;
                mend = mmid;
            } else {
                beg = mid;
                mbeg = mmid;
            }
        }
        return end;
    }

    // returns the left index of a right-cover
    private final int rcovj(double x) {
        int j = Arrays.binarySearch(cent, 0, nclusters, x);
        // exact match, return its index:
        if (j >= 0) return j;
        // x is not a cluster center, get its insertion index:
        j = -(j + 1);
        // x is to left of left-most cluster:
        if (j == 0) return -1;
        // return the index to the left of x:
        return j - 1;
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

    @Override
    public boolean equals(Object that) {
        if (!(that instanceof TDigest)) return false;
        if (this == that) return true;
        TDigest rhs = (TDigest)that;
        if (C != rhs.C) return false;
        if (maxDiscrete != rhs.maxDiscrete) return false;
        if (nclusters != rhs.nclusters) return false;
        if (M != rhs.M) return false;
        if (!equal(cent, rhs.cent, nclusters)) return false;
        if (!equal(mass, rhs.mass, nclusters)) return false;
        // if masses are equal, cumulative ftre had better also be equal
        return true;
    }

    // I can't believe java just added this to Arrays in java 9
    static final boolean equal(double[] lhs, double[] rhs, int n) {
        for (int j = 0; j < n; ++j) {
            if (lhs[j] != rhs[j]) return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int h = nclusters;
        h ^= doubleHash(M);
        if (nclusters >= 1) {
            h ^= doubleHash(cent[0]);
            h ^= doubleHash(mass[0]);
            h ^= doubleHash(ftre[1]);
        }
        if (nclusters >= 2) {
            h ^= doubleHash(cent[nclusters - 1]);
            h ^= doubleHash(mass[nclusters - 1]);
            h ^= doubleHash(ftre[nclusters]);
        }
        if (nclusters >= 3) {
            int j = nclusters / 2;
            h ^= doubleHash(cent[j]);
            h ^= doubleHash(mass[j]);
            h ^= doubleHash(ftre[1 + j]);
        }
        return h;
    }

    // I can't believe Double doesn't provide a static method for this
    static final int doubleHash(double x) {
        long v = Double.doubleToLongBits(x);
        return (int)(v ^ (v >>> 32));
    }

    /** Default for the maximum number of clusters */
    public static final int MAX_SIZE_DEFAULT = 100;

    /** Default for the initial cluster array capacity */
    public static final int INIT_SIZE_DEFAULT = 5;

    /** Obtain an empty t-digest with default maxsize and maximum discrete tracking. 
     * @return a new empty t-digest
     */
    public static TDigest empty() {
        return new TDigest(MAX_SIZE_DEFAULT, 0, INIT_SIZE_DEFAULT);
    }

    /**
     * Obtain an empty t-digest.
     * maxDiscrete defaults to zero.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @return a new empty t-digest
     */
    public static TDigest empty(int maxSize) {
        return new TDigest(maxSize, 0, INIT_SIZE_DEFAULT);
    }

    /**
     * Obtain an empty t-digest.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDiscrete maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     * @return a new empty t-digest
     */
    public static TDigest empty(int maxSize, int maxDiscrete) {
        return new TDigest(maxSize, maxDiscrete, INIT_SIZE_DEFAULT);
    }

    /**
     * Obtain an empty t-digest.
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDiscrete maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     * @param sz initial capacity to use for internal arrays. Must be &gt; 0.
     * @return a new empty t-digest
     */
    public static TDigest empty(int maxSize, int maxDiscrete, int sz) {
        return new TDigest(maxSize, maxDiscrete, sz);
    }

    /** Merge the argument with smaller mass into the one with larger mass, and return
     * the larger as the result.
     * Note this means either (ltd) or (rtd) will be modified.
     * @param ltd a t-digest
     * @param rtd another t-digest
     * @return if ltd has larger mass, then returns <pre>ltd.merge(rtd)</pre>,
     * otherwise <pre>rtd.merge(ltd)</pre>
     */
    public static TDigest merge(TDigest ltd, TDigest rtd) {
        if (ltd.size() < rtd.size()) return merge(rtd, ltd);
        if (rtd.size() == 0) return ltd;
        if (rtd.size() == 1) {
            ltd.update(rtd.cent[0], rtd.mass[0]);
            return ltd;
        }
        if (rtd.mass() < ltd.mass()) {
            ltd.merge(rtd);
            return ltd;
        } else {
            rtd.merge(ltd);
            return rtd;
        }
    }

    /**
     * Sketch data using a t-digest with default maxsize and maximum discrete tracking.
     * @param data the data to sketch
     * @return a t-digest sketch of the data
     */
    public static TDigest sketch(double[] data) {
        return sketch(data, MAX_SIZE_DEFAULT, 0, INIT_SIZE_DEFAULT);
    }

    /**
     * Sketch data using a t-digest.
     * maxDiscrete defaults to zero.
     * @param data the data to sketch
     * @param maxSize sketching maxSize setting.
     * Must be &gt; 0.
     * @return a t-digest sketch of the data
     */
    public static TDigest sketch(double[] data, int maxSize) {
        return sketch(data, maxSize, 0, INIT_SIZE_DEFAULT);
    }

    /**
     * Sketch data using a t-digest.
     * @param data the data to sketch
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDiscrete maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     * @return a t-digest sketch of the data
     */
    public static TDigest sketch(double[] data, int maxSize, int maxDiscrete) {
        return sketch(data, maxSize, maxDiscrete, INIT_SIZE_DEFAULT);
    }

    /**
     * Sketch data using a t-digest.
     * @param data the data to sketch
     * @param maxSize sketching maxsize setting.
     * Must be &gt; 0.
     * @param maxDiscrete maximum number of unique discrete values to track. Must be &ge; 0.
     * If this number of values is exceeded, the sketch will begin to operate in 
     * normal continuous mode.
     * @param sz initial capacity to use for internal arrays. Must be &gt; 0.
     * @return a t-digest sketch of the data
     */
    public static TDigest sketch(double[] data, int maxSize, int maxDiscrete, int sz) {
        TDigest td = empty(maxSize, maxDiscrete, sz);
        for (double x: data) td.update(x, 1.0);
        return td;
    }
}
