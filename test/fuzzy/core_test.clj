(ns fuzzy.core-test
  (:use [fuzzy.core] :reload-all)
  (:use [fuzzy.trie] :reload-all)
  (:use [clojure.test]))

(deftest test-construct-trie
  (testing "Construct trie"
    (is (= (construct-trie ["one" "to" "two"])

           {\t {\w {:re 2, :rs 2, :id 7,
                    \o {:id 8, :v "two", :t true}}, :re 2, :rs 1, :id 5,
                \o {:id 6, :v "to", :t true}},
            \o {:re 0, :rs 0, :id 2,
                \n {:re 0, :rs 0, :id 3,
                    \e {:id 4, :v "one", :t true}}}, :id 1, :seq 9, :rs -1, :re 2}))))

(deftest test-init-active-list
  (testing "Initiation of active list"
    (is (=
         (count (init-active-nodes (construct-trie ["one" "two" "three"]) 2))
         6))
    (is (=
         (count (init-active-nodes (construct-trie ["one" "two" "t"]) 2))
         4))))

(deftest test-del
  (let [active-nodes [[{} 1] [{} 2] [{} 0]]]
    (is (del active-nodes \s 2) '([{} 2] [{} 1]) )))

(deftest test-sub-match
  (let [eps (init-active-nodes (construct-trie ["lin" "liu" "luis"]) 2)
        eps1 (sub eps \s 2)]
    (do
      (is (= (count eps) 4))
      (is (= (count eps1) 3))
      (is (= (edit-dist (first eps1) ) 1))
      (is (= (edit-dist (first (rest eps1))) 2))

      (is (= (count (match eps \n 2)) 1))
      (is (= (count (match eps \s 2)) 0))

      (is (= (count (next-word eps \n 2)) 5))
      (is (= (count (next-word (next-word eps \n 2) \l 2)) 4))
      (is (= (count (next-word (next-word (next-word eps \n 2) \l 2) \i 2)) 6))
      (is (= (count (match (next-word (next-word eps \n 2) \l 2) \i 2)) 4))

      (is (= (count (next-word (next-word (next-word (next-word eps \n 2) \l 2) \i 2) \s 2)) 4))
      )))

(deftest test-fuzzy-find1
  (let [hs ["lin" "liu" "luis"]
        eps (init-active-nodes (construct-trie hs) 2)]
    (is (= (bounds (fuzzy-find "nlis" eps 2)) [0 2]))
    (is (= (spell "nlis" eps 2 hs) []))
    (is (= (complete "nlis" eps 2 hs) []))
    (is (= (bounds eps) [0 2]))))

(deftest test-fuzzy-find2
  (let [eps (init-active-nodes (construct-trie "resources/keywords") 2)
        hs (build-hash "resources/keywords")]
    (is (= (spell "walkz" eps 1 hs) []))
    (is (= (complete "rest" eps 1 hs) []))))
