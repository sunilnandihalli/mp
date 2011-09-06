(ns mp.core
  (:refer-clojure)
  (:gen-class)
  (:require [mp.debug :as d])
  (:import clojure.lang.MapEntry java.util.Map clojure.lang.PersistentTreeMap))


(declare pm-empty)

(deftype PersistentPriorityMap [priority->set-of-items item->priority __meta]
  Object
  (toString [this] (str (.seq this)))

  clojure.lang.ILookup
  ; valAt gives (get pm key) and (get pm key not-found) behavior
  (valAt [this item] (get item->priority item))
  (valAt [this item not-found] (get item->priority item not-found))

  clojure.lang.IPersistentMap
  (count [this] (count item->priority))

  (assoc [this item priority]
    (let [current-priority (get item->priority item nil)]
      (if current-priority
        ;Case 1 - item is already in priority map, so this is a reassignment
        (if (= current-priority priority)
          ;Subcase 1 - no change in priority, do nothing
          this
          (let [item-set (get priority->set-of-items current-priority)]
            (if (= (count item-set) 1)
              ;Subcase 2 - it was the only item of this priority
              ;so remove old priority entirely
              ;and conj item onto new priority's set
              (PersistentPriorityMap.
                (assoc (dissoc priority->set-of-items current-priority)
                  priority (conj (get priority->set-of-items priority #{}) item))
                (assoc item->priority item priority))
              ;Subcase 3 - there were many items associated with the item's original priority,
              ;so remove it from the old set and conj it onto the new one.
              (PersistentPriorityMap.
                (assoc priority->set-of-items
                  current-priority (disj (get priority->set-of-items current-priority) item)
                  priority (conj (get priority->set-of-items priority #{}) item))
                (assoc item->priority item priority)))))
        ; Case 2: Item is new to the priority map, so just add it.
        (PersistentPriorityMap.
          (assoc priority->set-of-items
            priority (conj (get priority->set-of-items priority #{}) item))
          (assoc item->priority item priority)))))

  (empty [this] pm-empty)

  ; cons defines conj behavior
  (cons [this e] (let [[item priority] e] (.assoc this item priority)))

  ; Like sorted maps, priority maps are equal to other maps provided
  ; their key-value pairs are the same.
  (equiv [this o] (.equiv item->priority o))
  (hashCode [this] (.hashCode item->priority))
  (equals [this o] (or (identical? this o) (.equals item->priority o)))

  ;containsKey implements (contains? pm k) behavior
  (containsKey [this item] (contains? item->priority item))

  (entryAt [this k]
    (let [v (.valAt this k this)]
      (when-not (identical? v this)
        (MapEntry. k v))))

  (seq [this]
    (seq (for [[priority item-set] priority->set-of-items, item item-set]
           (MapEntry. item priority))))

  ;without implements (dissoc pm k) behavior
  (without
    [this item]
    (let [priority (item->priority item ::not-found)]
      (if (= priority ::not-found)
	;; If item is not in map, return the map unchanged.
	this
	(let [item-set (priority->set-of-items priority)]
	  (if (= (count item-set) 1)
	    ;;If it is the only item with this priority, remove that priority's set completely
	    (PersistentPriorityMap. (dissoc priority->set-of-items priority)
				    (dissoc item->priority item))
	    ;;Otherwise, just remove the item from the priority's set.
	    (PersistentPriorityMap.
	     (assoc priority->set-of-items priority (disj item-set item)),
	     (dissoc item->priority item)))))))

  java.io.Serializable  ;Serialization comes for free with the other things implemented
  clojure.lang.MapEquivalence
  Map ;Makes this compatible with java's map
  (size [this] (count item->priority))
  (isEmpty [this] (zero? (count item->priority)))
  (containsValue [this v] (contains? (priority->set-of-items this) v))
  (get [this k] (.valAt this k))
  (put [this k v] (throw (UnsupportedOperationException.)))
  (remove [this k] (throw (UnsupportedOperationException.)))
  (putAll [this m] (throw (UnsupportedOperationException.)))
  (clear [this] (throw (UnsupportedOperationException.)))
  (keySet [this] (set (keys this)))
  (values [this] (vals this))
  (entrySet [this] (set this))

  clojure.lang.IPersistentStack
  (peek [this]
    (when-not (.isEmpty this)
      (let [f (first priority->set-of-items)]
        (MapEntry. (first (val f)) (key f)))))

  (pop [this]
    (if (.isEmpty this) (throw (IllegalStateException. "Can't pop empty priority map"))
      (let [f (first priority->set-of-items),
            item-set (val f)
            item (first item-set),
            priority (key f)]
        (if (= (count item-set) 1)
          ;If the first item is the only item with its priority, remove that priority's set completely
          (PersistentPriorityMap.
            (dissoc priority->set-of-items priority)
            (dissoc item->priority item))
          ;Otherwise, just remove the item from the priority's set.
          (PersistentPriorityMap.
            (assoc priority->set-of-items priority (disj item-set item)),
            (dissoc item->priority item))))))

  clojure.lang.IFn
  ;makes priority map usable as a function
  (invoke [this k] (.valAt this k))
  (invoke [this k not-found] (.valAt this k not-found))

  clojure.lang.IObj
  ;adds metadata support
  (meta [this] __meta)
  (withMeta [this m] (PersistentPriorityMap. priority->set-of-items item->priority m))

  clojure.lang.Reversible
  (rseq [this]
    (seq (for [[priority item-set] (rseq priority->set-of-items), item item-set]
           (MapEntry. item priority)))))

(def ^:private pm-empty (PersistentPriorityMap. (sorted-map) {} {}))
(defn- pm-empty-by [comparator] (PersistentPriorityMap. (sorted-map-by comparator) {}))

; The main way to build priority maps
(defn priority-map
  "keyval => key val
Returns a new priority map with supplied mappings"
  [& keyvals]
  (reduce conj pm-empty (partition 2 keyvals)))

(defn priority-map-by
  "keyval => key val
Returns a new priority map with supplied mappings"
  [comparator & keyvals]
  (reduce conj (pm-empty-by comparator) (partition 2 keyvals)))

(defmacro thrush-with-pattern [[pattern] first & exprs]
  (if (seq exprs) `(let [~pattern ~first] (thrush-with-pattern [~pattern] ~@exprs)) first))

(defmacro thrush-with-pattern-dbg [[pattern] first & exprs]
  (if (seq exprs) `(let [s# ~first
                         ~pattern s#]
                      (clojure.pprint/pprint ['~first s#])
                      (thrush-with-pattern-dbg [~pattern] ~@exprs)) first))


(defn read-stdin [& {:keys [fname] :or {fname "inp.txt"}}]
  (let [vs (or (seq (doall (line-seq (java.io.BufferedReader. *in*))))
               (seq (doall (line-seq (java.io.BufferedReader. (java.io.FileReader. fname))))))
        [[n] & nodes] (->> (map #(re-seq #"[^ ]+" %) vs)
                           (map #(map read-string %)))]
    [n (into [] (take n nodes))]))

(defn bounding-box [locs]
  (map #(apply (juxt min max) %) [(map first locs) (map second locs)]))

(defn int-str [i]
  (cond
   (< i 10) (str i " ")
   (< i 100) (str i)))

(defn display [locs-to-id locs]
  (let [[[xmin xmax] [ymin ymax]] (bounding-box locs)
        str (reduce (fn [cstr x]
                      (str cstr (apply str (interpose " " (map #(if-let [i (locs-to-id [x %])] (int-str i) ". ")
                                                               (range ymin (inc ymax))))) "\n")) "" (range xmin (inc xmax)))]
    (println str)))

(defn abs [a] (if (< a 0) (- a) a))

(defn brute-force-solve [locs]
  (let [mcost (fn [[x y]]
                (reduce (fn [cst [xi yi]]
                            (+ cst (max (abs (- x xi)) (abs (- y yi))))) 0 locs))]
    (apply min (map mcost locs))))

(defn solve []
  (let [[n locs] (time (read-stdin))
        locs (vec (map vec locs))
        [xsum ysum] (reduce (fn [[xsum ysum] [x y]]
                              [(+ xsum x) (+ ysum y)]) locs)
        [xav yav] [(/ xsum n) (/ ysum n)]
        [k-x+y k-x-y] [(+ xav yav) (- xav yav)]
        [dx+ dx- dy+ dy- x+y-coll x-y-coll] (reduce (fn [[dx+ dx- dy+ dy- x+y-coll x-y-coll cid] [x y]]
                                                      (let [x+y (+ x y)
                                                            x-y (- x y)
                                                            ncid (inc cid)]
                                                        (if (< x+y k-x+y)
                                                          (if (< x-y k-x-y)
                                                            [dx+ dx- dy+ (conj dy- cid) (conj x+y-coll x+y) (conj x-y-coll x-y) ncid] 
                                                            [dx+ (conj dx- cid) dy+ dy- (conj x+y-coll x+y) (conj x-y-coll x-y) ncid])
                                                          (if (< x-y k-x-y)
                                                            [dx+ dx- (conj dy+ cid) dy- (conj x+y-coll x+y) (conj x-y-coll x-y) ncid] 
                                                            [(conj dx+ cid) dx- dy+ dy- (conj x+y-coll x+y) (conj x-y-coll x-y) ncid]))))
                                                    [(vector-of :int) (vector-of :int) (vector-of :int)
                                                     (vector-of :int) (vector-of :int) (vector-of :int) 0] locs)
        [sum-dx+ sum-dx-] (map #(reduce (fn [s i]
                                          (let [[x _] (locs i)]
                                            (+ s x))) %) [dx+ dx-])
        [sum-dy+ sum-dy-] (map #(reduce (fn [s i]
                                          (let [[_ y] (locs i)]
                                            (+ s y))) %) [dy+ dy-])
        f-x+y-< #(< (x+y-coll %1) (x+y-coll %2))
        f-x-y-< #(< (x-y-coll %1) (x-y-coll %2))
        f-x+y-> #(> (x+y-coll %1) (x+y-coll %2))
        f-x-y-> #(> (x-y-coll %1) (x-y-coll %2))
        dx+-x+y (into (priority-map-by f-x+y-<) dx+)
        dx+-x-y (into (priority-map-by f-x-y-<) dx+)
        dx--x+y (into (priority-map-by f-x+y->) dx-)
        dx--x-y (into (priority-map-by f-x-y->) dx-)
        dy+-x+y (into (priority-map-by f-x+y-<) dy+)
        dy+-x-y (into (priority-map-by f-x-y->) dy+)
        dy--x+y (into (priority-map-by f-x+y->) dy-)
        dy--x-y (into (priority-map-by f-x-y-<) dy-)
        
        cost (fn cost [mp]
               (- (+ (get-in mp [:dx :+ :sum])
                     (get-in mp [:dy :+ :sum]))
                  (+ (get-in mp [:dx :- :sum])
                     (get-in mp [:dy :- :sum]))))

     
        hash-coll {:x+y x+y-coll :x-y x-y-coll}
        node-movement-map {:x+y {:dec [{:from [:dy :-] :to [:dx :+]}
                                       {:from [:dx :-] :to [:dy :+]}]
                                 :inc [{:from [:dx :+] :to [:dy :-]}
                                       {:from [:dy :+] :to [:dx :-]}]}
                           :x-y {:dec [{:from [:dy :+] :to [:dx :+]}
                                       {:from [:dx :-] :to [:dy :-]}]
                                 :inc [{:from [:dx :+] :to [:dy :+]}
                                       {:from [:dy :-] :to [:dx :-]}]}}
        move (fn move [[dir inc-or-dec] mp]
               {:post [(clojure.inspector/inspect-tree {:before (d/self-keyed-map dir inc-or-dec mp locs)
                                                        :after %})]}
               (let [[opt1 opt2 :as opts] (get-in node-movement-map [dir inc-or-dec])
                     [s1 s2] (map #(get-in mp (:from %)) opts)
                     [h1 h2] (map #((hash-coll dir) (first (% dir))) [s1 s2])
                     execute-option (fn execute-option [{:keys [from to] :as opt}]
                                      (let [mdisj (fn mdisj [dx-or-dy id m]
                                                    (-> m
                                                        (update-in [:x+y] #(disj % id))
                                                        (update-in [:x-y] #(disj % id))
                                                        (update-in [:sum] #(case dx-or-dy
                                                                                 :dx (let [[x _] (locs id)] (- % x))
                                                                                 :dy (let [[_ y] (locs id)] (- % y))))))
                                            mconj (fn mconj [dx-or-dy id m]
                                                    (-> m
                                                        (update-in [:x+y] #(conj % id))
                                                        (update-in [:x-y] #(conj % id))
                                                        (update-in [:sum] #(case dx-or-dy
                                                                                 :dx (let [[x _] (locs id)] (+ % x))
                                                                                 :dy (let [[_ y] (locs id)] (+ % y))))))
                                            id (first (get-in mp (conj from dir)))]
                                        (-> mp
                                            (update-in from #(mdisj (first from) id %))
                                            (update-in to #(mconj (first to) id %)))))]
                 (execute-option (if ((case inc-or-dec :inc < :dec >) h1 h2) opt1 opt2))))
        optimize-along-dir (fn optimize [optimization-dir mp]
                             (let [helper (fn helper [hmp inc-or-dec]
                                            (let [nhmp (move [optimization-dir inc-or-dec] hmp)
                                                  cst-nhmp (cost nhmp)
                                                  cst-hmp (cost hmp)]
                                              (if (> cst-nhmp cst-hmp) hmp
                                                  (recur nhmp inc-or-dec))))
                                   mp-inc (helper mp :inc)
                                   cst-mp (cost mp)
                                   cst-mp-inc (cost mp-inc)]
                               (if (= cst-mp-inc cst-mp)
                                 (helper cst-mp :dec) mp-inc)))
        mp {:dx {:+ {:x+y dx+-x+y :x-y dx+-x-y :sum sum-dx+}
                 :- {:x+y dx--x+y :x-y dx--x-y :sum sum-dx-}}
            :dy {:+ {:x+y dy+-x+y :x-y dy+-x-y :sum sum-dy+}
                 :- {:x+y dy--x-y :x-y dy--x-y :sum sum-dy-}}}
        min-mp (loop [cur-mp mp]
                 (let [new-mp (->> mp (optimize-along-dir :x+y) (optimize-along-dir :x-y))]
                   (if (= new-mp mp) mp (recur new-mp))))]
    (println (cost min-mp))))
                
        
             

(defn -main []
  (solve))
