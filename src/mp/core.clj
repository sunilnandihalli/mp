(ns mp.core
  (:refer-clojure)
  (:gen-class)
  (:require [mp.debug :as d])
  (:import clojure.lang.MapEntry java.util.Map clojure.lang.PersistentTreeMap
           (clojure.lang Seqable Sequential ISeq IPersistentSet ILookup
                         IPersistentStack IPersistentCollection Associative
                         Sorted Reversible Indexed Counted)))




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
    
(defn solve []
  (let [[n locs] (read-stdin)
        locs (vec (map vec locs))
        locs-to-id (into {} (map vector locs (range)))
        [[xmin xmax] [ymin ymax]] (bounding-box locs)
        front-node-priority (fn [p-1 p p+1]
                              (if-not p nil
                                      (let [[[x-1 y-1] [x y] [x+1 y+1]] (map locs [p-1 p p+1])
                                            prty (apply min (keep identity [(when (and p-1 p+1 (> x-1 x) (> x+1 x)) (+ x (- y+1 y-1)))
                                                                            (when (and p-1 p+1 (= x-1 x x+1)) (+ xmax 10))
                                                                            (when (and p+1 (> x+1 x)) (+ x (* 2 (- y+1 ymin))))
                                                                            (when (and p-1 (> x-1 x)) (+ x (* 2 (- ymax y-1))))
                                                                            (+ xmax 10)]))]
                                        prty)))
        points-on-either-side (fn [front p n]
                                (let [[x0 y0] (locs p)
                                      before-p (take n (map second (rsubseq front < y0)))
                                      after-p (take n (map second (subseq front > y0)))]
                                  (concat (reverse before-p) [p] after-p)))
        update-priorities (fn [pf affected-nodes]
                            (let [affected-triplets (partition 3 1 affected-nodes)]
                              (reduce (fn [cpf [p-1 p p+1]]
                                        (assoc cpf p (front-node-priority p-1 p p+1))) pf affected-triplets)))
        add-node (fn add-node [w [cx cy :as np]]
                   (let [new-node-id (locs-to-id np)]
                     (thrush-with-pattern [{:keys [front pfront graph-edges] :as w}] w
                       (if-let [p (front cy)]
                         (let [[p-2 p-1 p p+1 p+2] (points-on-either-side front p 2)]
                           (thrush-with-pattern [w]
                             (update-in w [:graph-edges] #(into % [[p new-node-id] [p-1 new-node-id] [p+1 new-node-id]]))
                             (assoc w [:front cy] new-node-id)
                             (update-in w [:pfront] #(update-priorities % [p-2 p-1 new-node-id p+1 p+2]))))
                         (thrush-with-pattern [w]
                           (assoc-in w [:front cy] new-node-id)
                           (let [[p-2 p-1 p p+1 p+2] (points-on-either-side new-node-id)]
                             (update-in w [:pfront] #(update-priorities % [p-2 p-1 new-node-id p+1 p+2]))))))
                     (loop [{ge :graph-edges f :front pf :pfront} w]
                       (let [[cid s-max] (peek pf)]
                         (if (< cx s-max) w
                             (let [[p-2 p-1 p p+1 p+2] (points-on-either-side cid 2)
                                   [x y] (locs cid)
                                   new-f (dissoc f y)
                                   new-pf (-> (dissoc pf p) (update-priorities [p-2 p-1 p+1 p+2]))
                                   new-ge (conj ge [p-1 p+1])]
                               (recur {:front new-f :pfront new-pf :graph-edges new-ge})))))))
        [[_ fy :as floc] & rlocs] (sort locs)
        fid (locs-to-id floc)
        {vornoi-graph-edges :graph-edges} (reduce #(do (clojure.inspector/inspect-tree {:cur %1 :new-node %2 :locs locs :locs-to-id locs-to-id})
                                                       (add-node %1 %2)) {:front (sorted-map fy fid) :pfront (priority-map fid xmax) :graph-edges []} rlocs)
        vornoi-graph  (reduce (fn vornoi-graph-reduction-func [g [x y :as w]]
                                (-> (update-in g [x] #(conj % y)) (update-in [y] #(conj % x)))) {} vornoi-graph-edges)
        vornoi-graph-edges (into #{} (map set vornoi-graph-edges))
        abs (fn [a] (if (< a 0) (- a) a))
        cost (memoize (fn [i]
                        (if-not (integer? i) (do (clojure.inspector/inspect-tree (d/self-keyed-map i))
                                                 (throw (Exception. "errror")))
                                (let [[x0 y0] (locs i)]
                                  (reduce + (map (fn [[x y]] (max (abs (- x x0)) (abs (- y y0)))) locs))))))
        _ (clojure.inspector/inspect-tree (d/self-keyed-map vornoi-graph vornoi-graph-edges))
        min-node-id (loop [cur-i 0]
                      (let [cur-cost (cost cur-i)]
                        (println (d/self-keyed-map cur-i cur-cost)))
                      (let [nbrs (vornoi-graph cur-i)
                            min-nbr (apply min-key cost nbrs)]
                        (if (< (cost min-nbr) (cost cur-i))
                          (recur min-nbr) cur-i)))
        brute-force-min-id (apply min-key cost (range (count locs)))]
    (display locs-to-id locs)
    (println {min-node-id (cost min-node-id)
              brute-force-min-id (cost brute-force-min-id)})))

(defn -main [])
