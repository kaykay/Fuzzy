(ns fuzzy.core
  (:require [fuzzy.trie]
            [clojure.pprint]
            [clojure.contrib.profile]
            [compojure.route :as route]
            )
  (:import (java.io BufferedReader FileReader))
  (use criterium.core
       compojure.core
       ring.adapter.jetty
       clojure.contrib.json))


(defn filter-un [coll]
  (filter (fn [item] (coll? item)) (vals coll)))

(defn nodes-at-dist [coll dist]
  "Takes a sub-trie and returns all the active list style collection with level as the delta"
  (map (fn [v] [v dist]) (filter-un coll)))

(comment (defn init-active-nodes [tri]
  "initial active list, delta hardcoded to 2, need to generalize it"
  (conj (concat (nodes-at-dist tri 1) 
                (reduce concat (map (fn [i] (concat (nodes-at-dist i 2))) (filter-un tri))))
        [tri 0])))

(defn edit-dist [node-pair]
  (last node-pair))

(defn filter-1-less [active-nodes-coll delta]
  "Filters all the active-node pairs whose edit distance is equal to delta or greater"
  (filter (fn [node-pair] (< (edit-dist node-pair) delta)) active-nodes-coll))

(defn del [active-nodes-coll letter delta]
  (vec (map (fn [node-pair]
         [(first node-pair) (+ (last node-pair) 1)])
       (filter-1-less active-nodes-coll delta))))

(defn sub [active-nodes-coll letter delta]
  (vec (reduce concat
               (map (fn [active-node-pair]
                      (nodes-at-dist (first active-node-pair) (+ 1 (last active-node-pair))))
                    (filter-1-less active-nodes-coll delta)))))

(defn insert [[node dist] delta]
  (loop [res [] queue [[node dist]]]
    (let [first-in-queue (first queue)]
      (if (not (nil? first-in-queue)) 
        (if (< (last first-in-queue) delta)
          (recur (conj res first-in-queue) (concat (vec (rest queue)) (map (fn [f] [f (+ 1 (last first-in-queue))]) (filter-un (first first-in-queue)))) )
          (recur (conj res first-in-queue) (vec (rest queue)) ))
        res))))

(defn match [active-nodes-coll letter delta]
  (reduce  (fn [val active-node-pair]
             (if (nil? ((first active-node-pair) letter))
               val
               (concat val (insert [((first active-node-pair) letter) (last active-node-pair)] delta)))) [] active-nodes-coll))

(defn active-list-node-id [active-list-node]
  (:id (first active-list-node)))

(def active-list-comp-proxy (proxy [java.util.Comparator] []
                              (compare [o1 o2]
                                       (cond
                                        (< (active-list-node-id o1) (active-list-node-id o2)) -1 
                                        (> (active-list-node-id o1) (active-list-node-id o2)) 1 
                                        (= (active-list-node-id o1) (active-list-node-id o2)) 0 ))
                              (equals [o1]
                                      (if (= (active-list-node-id this) (active-list-node-id o1))
                                        true
                                        false))))

(def active-list-edit-comp-proxy (proxy [java.util.Comparator] []
                              (compare [o1 o2]
                                       (cond
                                        (< (last o1) (last o2)) -1 
                                        (> (last o1) (last o2)) 1 
                                        (= (last o1) (last o2)) 0 ))
                              (equals [o1]
                                      (if (= (last this) (last o1))
                                        true
                                        false))))

(defn init-active-nodes [tri delta]
  (insert [tri 0] delta))

(defn merge-node [coll active-node]
  "Merge an active node into a vector of active nodes"
  (loop [i 0]
    (if (< i (count coll))
      (if (= (:id (first (nth coll i))) (:id (first active-node)))
        (if (<= (last (nth coll i)) (last active-node))
          coll
          (assoc (vec coll) i active-node))
        (recur (+ 1 i)))
      (conj coll active-node))))


(defn merge-2-node-cols [col1 col2]
  "Merges 2 sorted active node pair collections"
  (loop [ind1 0 ind2 0 res []]
    (if (and (>= ind1 (count col1)) (>= ind2 (count col2)))
      res
      (cond (< (active-list-node-id (nth col1 ind1)) (active-list-node-id (nth  col2 ind2)))
            (recur (inc ind1) ind2 (conj res (nth col1 ind1)))
            (< (active-list-node-id (nth col1 ind1)) (active-list-node-id (nth  col2 ind2)))
            (recur ind1 (inc ind2) (conj res (nth  col2 ind2)))
            (= (active-list-node-id (nth  col1 ind2)) (active-list-node-id (nth col2 ind2)))
            (recur ind1 (inc ind2) res)
            ))))

(defn merge-nodes [coll]
  "merges active node pair collections"
  (vec (reduce (fn [res coll]
                 (reduce merge-node res coll)) coll)))



(defn next-word [active-nodes letter delta]
  (merge-nodes (vec (map (fn [meth] (meth active-nodes letter delta)) [del sub match]))))

(comment (def trie (construct-trie "resources/keywords_s")))

(comment (def eps0 (init-active-nodes trie 2)))

(defn fuzzy-find [word eps delta]
  (time (reduce (fn [val letter] (next-word val letter delta)) eps word)))

(defn spell [word eps delta hsh]
  "Spells, gets the terminals in the active nodes returned by running fuzzy find "
  (map (fn [i] [(get hsh (:v (first i))) (last i)])
       (filter (fn [m] (:t (first m))) (fuzzy-find word eps delta))))

(defn bounds1 [b1 b2]
  (let [s (if (< (first b1) (first b2)) (first b1) (first b2))
        e (if (> (last b1) (last b2)) (last b1) (last b2))]
    [s e]))

(defn bounds1 [eps]
     (map
      (fn [e] [(:rs (first e)) (:re (first e))] ) eps))

(defn firstn [bnds cnt]
  (take cnt
        (reduce concat
                (map
                 (fn [bnd] (range (first bnd) (inc (last bnd)))) bnds) )))

(defn bounds [eps]
  (reduce
   (fn [v, n] (let [rs (:rs (first n))
                    re (:re  (first n))
                    s (if (< rs (first v)) rs (first v))
                    e (if (> re (last v)) re (last v))]
                [s e])) [(:rs (first (first eps))) (:re (first (first eps)))] eps))
(defn rank [bnds hs]
  (map (fn [i] (nth hs i)) (firstn bnds 5)))

(defn complete [word eps delta hsh]
  (time (rank (bounds1 ( sort active-list-edit-comp-proxy (fuzzy-find word eps delta))) hsh)))

(defn cache2steps [trie delta]
  )


(def eps (init-active-nodes (fuzzy.trie/construct-trie "resources/keywords") 1 ))
(def hs (fuzzy.trie/build-hash "resources/keywords"))

(defroutes main
  (GET "/complete" [p]
       (json-str (complete p eps 1 hs)))
       (route/not-found "Page not found")) 


(future (run-jetty (var main) {:port 5000}))
