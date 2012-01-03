(ns fuzzy.trie
  (:import (java.io BufferedReader FileReader)))

(comment (defn add-to-trie [trie x]
  (assoc-in trie x (merge (get-in trie x) {:v x :t true}))))

(defn insert-word [trie [w & ws] v id hid]
  (if ws
    (if (get trie w)
      (let [inter (insert-word (get trie w) ws v id hid)]
        [(assoc trie w (assoc (first inter) :re hid)) (last inter)])
      (let [inter (insert-word (get trie w) ws v (+ id 1) hid)]
        [(assoc trie w (assoc (first inter) :id id :rs hid :re hid)) (last inter)]))
     [(assoc trie w (assoc v :id id)) (+ id 1)]))

(defn add-to-trie [trie w]  
  (let [hid (+ 1 (:re trie))
        inter (insert-word (assoc trie :re hid) w {:v hid :t true :rs hid :re hid} (:seq trie) hid)
        ]
    (assoc (first inter) :seq (last inter))))

(defn build-trie [coll]
  "Builds a trie over the values in the specified seq coll."
  (reduce add-to-trie {:id 1 :seq 2 :rs  0 :re -1} coll))

(defmulti construct-trie class)

(defmethod construct-trie String [file-name]
  (with-open [rdr (BufferedReader. (FileReader. file-name))]
    (build-trie (line-seq rdr))))

(defn build-hash [file-name]
  (with-open [rdr (BufferedReader. (FileReader. file-name))]
    (vec (line-seq rdr))))

(defmethod construct-trie clojure.lang.PersistentVector [keywords]
  (build-trie keywords))
