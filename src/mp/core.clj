(ns mp.core
  (:refer-clojure)
  (:gen-class)
  (:require [mp.debug :as d]
            [clojure.set :as s])
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

(defn bounding-box
  ([locs b]
     (map (fn [x] (apply (juxt (comp #(- % b) min) (comp #(+ % b) max)) x))
          [(map first locs) (map second locs)]))
  ([locs]
     (bounding-box locs 0)))

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
    (apply min-key second (map (juxt identity mcost) locs))))
(def node-movement-map {:x+y {:dec [{:from [:dy :-] :to [:dx :+]}
                                    {:from [:dx :-] :to [:dy :+]}]
                              :inc [{:from [:dx :+] :to [:dy :-]}
                                    {:from [:dy :+] :to [:dx :-]}]}
                        :x-y {:dec [{:from [:dy :+] :to [:dx :+]}
                                    {:from [:dx :-] :to [:dy :-]}]
                              :inc [{:from [:dx :+] :to [:dy :+]}
                                    {:from [:dy :-] :to [:dx :-]}]}})
      
(defn are-there-points-in-intended-direction-of-movement [[dir inc-or-dec] mp]
  (some #(seq (:x+y (get-in mp (:from %)))) (get-in node-movement-map [dir inc-or-dec])))

(defn solve []
  (let [[n locs] (time (read-stdin))
        locs (vec (map vec locs))
        [[xmin xmax] [ymin ymax]] (bounding-box locs 2)
        [[lim-x+y-min lim-x+y-max] [lim-x-y-min lim-x-y-max]] [[(+ xmin ymin) (+ xmax ymax)] [(- xmin ymax) (- xmax ymin)]]
        locs-to-id (into {} (map vector locs (range)))
        hashes-to-id (into {} (map (fn [[x y] i]
                                     [[(+ x y) (- x y)] i]) locs (range)))
        [xsum ysum] (reduce (fn [[xsum ysum] [x y]] [(+ xsum x) (+ ysum y)]) locs)
        [xav yav] [(/ xsum n) (/ ysum n)]
        [k-x+y k-x-y] [(+ xav yav) (- xav yav)]
        [dx+ dx- dy+ dy- x+y-coll x-y-coll] (reduce (fn [[dx+ dx- dy+ dy- x+y-coll x-y-coll cid] [x y]]
                                                      (let [x+y (+ x y)
                                                            x-y (- x y)
                                                            n-x+y-coll (conj x+y-coll x+y)
                                                            n-x-y-coll (conj x-y-coll x-y)
                                                            ncid (inc cid)]
                                                        (if (< x+y k-x+y)
                                                          (if (< x-y k-x-y)
                                                            [dx+ dx- dy+ (conj dy- cid) n-x+y-coll n-x-y-coll ncid] 
                                                            [dx+ (conj dx- cid) dy+ dy- n-x+y-coll n-x-y-coll ncid])
                                                          (if (< x-y k-x-y)
                                                            [dx+ dx- (conj dy+ cid) dy- n-x+y-coll n-x-y-coll ncid] 
                                                            [(conj dx+ cid) dx- dy+ dy- n-x+y-coll n-x-y-coll ncid]))))
                                                    (conj (vec (repeatedly 6 #(vector-of :int))) 0) locs)
                                        ;_ (clojure.inspector/inspect-tree (d/self-keyed-map dx+ dx- dy+ dy-))
        [sum-dx+ sum-dx-] (map #(reduce (fn [s i]
                                          (let [[x _] (locs i)]
                                            (+ s x))) 0 %) [dx+ dx-])
        [sum-dy+ sum-dy-] (map #(reduce (fn [s i]
                                          (let [[_ y] (locs i)]
                                            (+ s y))) 0 %) [dy+ dy-])
        
        dx+-x+y (into (priority-map-by <) (map (juxt identity x+y-coll) dx+))
        dx+-x-y (into (priority-map-by <) (map (juxt identity x-y-coll) dx+))
        dx--x+y (into (priority-map-by >) (map (juxt identity x+y-coll) dx-))
        dx--x-y (into (priority-map-by >) (map (juxt identity x-y-coll) dx-))
        dy+-x+y (into (priority-map-by <) (map (juxt identity x+y-coll) dy+))
        dy+-x-y (into (priority-map-by >) (map (juxt identity x-y-coll) dy+))
        dy--x+y (into (priority-map-by >) (map (juxt identity x+y-coll) dy-))
        dy--x-y (into (priority-map-by <) (map (juxt identity x-y-coll) dy-))
        
        cost-fn (fn cost-fn [mp]
                  {:pre [mp #_(do (clojure.pprint/pprint mp) true)]
                   :post [#_(d/d {:mp mp :cost-fn %})]}
                  (let [k (- (+ (get-in mp [:dx :+ :sum])
                                (get-in mp [:dy :+ :sum]))
                             (+ (get-in mp [:dx :- :sum])
                                (get-in mp [:dy :- :sum])))
                        min-x+y (apply max
                                       (keep identity [(second (first (get-in mp [:dx :- :x+y])))
                                                       (second (first (get-in mp [:dy :- :x+y])))
                                                       lim-x+y-min]))
                        max-x+y (apply min
                                       (keep identity [(second (first (get-in mp [:dx :+ :x+y])))
                                                       (second (first (get-in mp [:dy :+ :x+y])))
                                                       lim-x+y-max]))
                        min-x-y (apply max
                                       (keep identity [(second (first (get-in mp [:dx :- :x-y])))
                                                       (second (first (get-in mp [:dy :+ :x-y])))
                                                       lim-x-y-min]))
                        max-x-y (apply min
                                       (keep identity [(second (first (get-in mp [:dx :+ :x-y])))
                                                       (second (first (get-in mp [:dy :- :x-y])))
                                                       lim-x-y-max]))
                        nx- (count (get-in mp [:dx :- :x+y]))
                        nx+ (count (get-in mp [:dx :+ :x+y]))
                        ny- (count (get-in mp [:dy :- :x+y]))
                        ny+ (count (get-in mp [:dy :+ :x+y]))
                        map-hash [(/ (+ min-x+y max-x+y) 2) (/ (+ min-x-y max-x-y) 2)] 
                        y-coeff (- ny- ny+) x-coeff (- nx- nx+)
                        x+y-coeff (/ (+ x-coeff y-coeff) 2) x-y-coeff (/ (- x-coeff y-coeff) 2)]
                    {:k k :y-coeff y-coeff :x-coeff x-coeff :x+y-coeff x+y-coeff :x-y-coeff x-y-coeff :map-hash map-hash
                     :min-x+y  min-x+y :max-x+y max-x+y :min-x-y  min-x-y :max-x-y max-x-y}))
        
        corners-of-cost-func (fn [{:keys [k x+y-coeff x-y-coeff min-x+y max-x+y min-x-y max-x-y] :as w}]
                               {:pre [#_(clojure.inspector/inspect-tree (d/self-keyed-map k x+y-coeff x-y-coeff min-x+y max-x+y min-x-y max-x-y w))
                                      w k x+y-coeff x-y-coeff min-x+y max-x+y min-x-y max-x-y]
                                :post [#_(d/d {:inp w :ret % :locs-to-id locs-to-id})]}
                               (let [cost (fn [x+y x-y] (+ k (* x+y-coeff x+y) (* x-y-coeff x-y)))]
                                 (for [x+y [min-x+y max-x+y]
                                       x-y [min-x-y max-x-y]]
                                   [[x+y x-y] (cost x+y x-y)])))
        hash-coll {:x+y x+y-coll :x-y x-y-coll}
        move (fn move [[dir inc-or-dec] mp]
               {:post [#_(clojure.inspector/inspect-tree {:before (d/self-keyed-map dir inc-or-dec mp locs) :after %})
                       #_(or (clojure.pprint/pprint {:before (d/self-keyed-map dir inc-or-dec mp locs) :after %}) true) mp]}
               (when (and dir inc-or-dec mp (are-there-points-in-intended-direction-of-movement [dir inc-or-dec] mp))
                 (let [execute-option (fn execute-option [cmp  [id {:keys [from to] :as opt}]]
                                        {:post [cmp %]}
                                        (let [mdisj (fn mdisj [dx-or-dy m]
                                                      (-> m
                                                          (update-in [:x+y] #(dissoc % id))
                                                          (update-in [:x-y] #(dissoc % id))
                                                          (update-in [:sum] #(case dx-or-dy
                                                                                   :dx (let [[x _] (locs id)] (- % x))
                                                                                   :dy (let [[_ y] (locs id)] (- % y))))))
                                              mconj (fn mconj [dx-or-dy m]
                                                      (-> m
                                                          (update-in [:x+y] #(assoc % id (x+y-coll id)))
                                                          (update-in [:x-y] #(assoc % id (x-y-coll id)))
                                                          (update-in [:sum] #(case dx-or-dy
                                                                                   :dx (let [[x _] (locs id)] (+ % x))
                                                                                   :dy (let [[_ y] (locs id)] (+ % y))))))]
                                          (-> cmp
                                              (update-in from #(mdisj (first from) %))
                                              (update-in to #(mconj (first to) %)))))
                       [opt1 opt2 :as opts] (get-in node-movement-map [dir inc-or-dec])
                       inc-or-dec-fn ({:inc < :dec >} inc-or-dec)]
                   (loop [ccmp mp old-hash-val nil]
                     #_(clojure.pprint/pprint (d/self-keyed-map ccmp old-hash-val opts inc-or-dec dir))
                     (let [[s1 s2] (map #(get-in ccmp (:from %)) opts)
                           [[id1 h1 :as fs1] [id2 h2 :as fs2]] (map (comp peek dir) [s1 s2])]
                       (if-let [[[id h] copt] (cond
                                               (and fs1 fs2) (if (inc-or-dec-fn h1 h2) [fs1 opt1] [fs2 opt2])
                                               fs1 [fs1 opt1] fs2 [fs2 opt2])]
                         (if-not (or (not old-hash-val) (= old-hash-val h)) ccmp
                                 (recur (execute-option ccmp [id copt]) h))
                         ccmp))))))
        sgn (fn sgn [x] (cond (< x 0) :neg (> x 0) :pos :else :zero))
        optimize (fn optimize [mp]
                   (loop [{:keys [x+y-coeff x-y-coeff] :as cst-cmp} (cost-fn mp) cmp mp [min-xy min-cost] nil]
                     (println (d/self-keyed-map min-xy min-cost))
                     (let [[opt1 opt2 :as opts] (filter second [[:x+y (cond
                                                                       (> x+y-coeff 0) :dec
                                                                       (< x+y-coeff 0) :inc)]
                                                                [:x-y (cond
                                                                       (> x-y-coeff 0) :dec
                                                                       (< x-y-coeff 0) :inc)]])]
                       (if-let [mps (seq (keep #(move % cmp) opts))]
                         (let [[new-cost-fn new-mp [new-min-xy new-min-cost]] (apply min-key (fn [[_ _ [_ x]]] x) 
                                                                                     (map (fn [mp]
                                                                                            (let [cst-fnc (cost-fn mp)
                                                                                                  min-corner (apply min-key second (corners-of-cost-func cst-fnc))]
                                                                                              [cst-fnc mp min-corner])) mps))]
                           (if (not (or (not min-cost) (< new-min-cost min-cost))) cmp
                               (recur new-cost-fn new-mp [new-min-xy new-min-cost]))) cmp))))
        mp {:dx {:+ {:x+y dx+-x+y :x-y dx+-x-y :sum sum-dx+}
                 :- {:x+y dx--x+y :x-y dx--x-y :sum sum-dx-}}
            :dy {:+ {:x+y dy+-x+y :x-y dy+-x-y :sum sum-dy+}
                 :- {:x+y dy--x-y :x-y dy--x-y :sum sum-dy-}}}
        min-mp (optimize mp)
        min-map-cost-func (cost-fn min-mp)
        starting-point-front (into (priority-map) (corners-of-cost-func min-map-cost-func))
        maps-with-cost-increasing-envelope (loop [map-collection #{min-mp}  [fmap-front & rmaps-front] [min-mp]]
                                             (if-not fmap-front map-collection
                                                     (let [{:keys [x+y-coeff x-y-coeff]} (cost-fn fmap-front)
                                                           new-maps (filter (comp not map-collection)
                                                                            (keep #(move % fmap-front)
                                                                                  [[:x+y (cond
                                                                                          (< x+y-coeff 0) :inc
                                                                                          (> x+y-coeff 0) :dec)]
                                                                                   [:x-y (cond
                                                                                          (< x-y-coeff 0) :inc
                                                                                          (> x-y-coeff 0) :dec)]]))]
                                                       (recur (into map-collection new-maps) (into rmaps-front new-maps)))))
                       
        [points-priority-map
         point-contributed-by-maps
         map-contributes-points
         map-hash-to-map] (reduce (fn [[ppl pcbm mcp mhtm] cmp]
                                    (let [{:keys [max-x+y min-x+y max-x-y min-x-y map-hash] :as cfn} (cost-fn cmp)
                                          point-priority-pairs (corners-of-cost-func cfn)]
                                      (conj (reduce (fn [[cppl cpcbm cmcp] [hash-coord prty :as pp]]
                                                      [(conj cppl pp)
                                                       (update-in cpcbm [hash-coord] #(conj (or % #{}) map-hash))
                                                       (update-in cmcp [map-hash] #(conj (or % #{}) hash-coord))])
                                                    [ppl pcbm mcp]
                                                    point-priority-pairs) (assoc mhtm map-hash cmp))))
         [(priority-map) {} {} {}] maps-with-cost-increasing-envelope) 
        [min-point min-cost] (loop [cur-points-priority-map points-priority-map
                                    cur-point-contributed-by-maps point-contributed-by-maps
                                    cur-map-contributes-points map-contributes-points
                                    cur-map-hash-to-map map-hash-to-map]
                               (let [[cur-optimum-point-hash cur-point-cost :as w] (peek cur-points-priority-map)]
                                 (if (hashes-to-id cur-optimum-point-hash) w
                                     (let [maps-contributing-current-point (set (cur-point-contributed-by-maps cur-optimum-point-hash))
                                           advance-map (fn advance-map [[mcp pcbm ppm mhtm] leaving-map-hash]
                                                         {:pre [#_(or (println (d/self-keyed-map leaving-map-hash mcp ppm mhtm)) true)]
                                                          :post [#_(d/d {:before (d/self-keyed-map mcp pcbm ppm mhtm leaving-map-hash)
                                                                         :after (let [[mcp pcbm ppm mhtm] %]
                                                                                  (d/self-keyed-map mcp pcbm ppm mhtm))})]}
                                                         (let [leaving-map (mhtm leaving-map-hash)
                                                               {:keys [x+y-coeff x-y-coeff] :as lmcfn} (cost-fn leaving-map)  
                                                               opts (let [switcher (comp {1 [:inc] -1 [:dec] 0 [:inc :dec]} #(compare % 0))]
                                                                      (concat (map #(vector :x+y %) (switcher x+y-coeff))
                                                                              (map #(vector :x-y %) (switcher x-y-coeff))))
                                                               new-pcbm (reduce (fn [npcbm pt]
                                                                                  (let [npcbm-pt (npcbm pt)
                                                                                        new-npcbm-pt (disj npcbm-pt leaving-map-hash)]
                                                                                    (if-not (seq new-npcbm-pt) (dissoc npcbm pt)
                                                                                            (assoc npcbm pt new-npcbm-pt)))) pcbm
                                                                                            (mcp leaving-map-hash))
                                                               new-mcp (dissoc mcp leaving-map-hash)
                                                               new-map-hash-map-pairs (filter (comp not mhtm first)
                                                                                              (map (juxt (comp :map-hash cost-fn) identity)
                                                                                                   (keep #(move % leaving-map) opts)))
                                                               [nnn-pcbm nnn-mcp nnn-pp nnn-mhtm] (reduce (fn [[n-pcbm n-mcp n-pp n-mhtm] [mp-hash mp]]
                                                                                                            (let [map-cost-fn (cost-fn mp)
                                                                                                                  point-priority-pairs (corners-of-cost-func map-cost-fn)
                                                                                                                  nn-pcbm (reduce
                                                                                                                           (fn [cn-pcbm [pt-hash _]]
                                                                                                                             (update-in cn-pcbm [pt-hash]
                                                                                                                                        #(conj (or % #{}) mp-hash)))
                                                                                                                           n-pcbm point-priority-pairs)
                                                                                                                  nn-mcp (assoc n-mcp mp-hash
                                                                                                                                (set (map first point-priority-pairs)))
                                                                                                                  nn-pp (into n-pp point-priority-pairs)
                                                                                                                  nn-mhtm (assoc n-mhtm mp-hash mp)]
                                                                                                              [nn-pcbm nn-mcp nn-pp nn-mhtm]))
                                                                                                          [new-pcbm new-mcp ppm (dissoc mhtm leaving-map-hash)]
                                                                                                          new-map-hash-map-pairs)]
                                                           [nnn-mcp nnn-pcbm nnn-pp nnn-mhtm]))
                                           [new-map-contributes-points new-point-contributed-by-maps new-points-priority-map new-map-hash-to-map]
                                           (reduce advance-map [cur-map-contributes-points cur-point-contributed-by-maps (pop cur-points-priority-map) cur-map-hash-to-map]
                                                   maps-contributing-current-point)]
                                       (recur new-points-priority-map new-point-contributed-by-maps new-map-contributes-points new-map-hash-to-map)))))]
    (let [[bf-min-loc bf-min-cost] (brute-force-solve locs)]
      (display locs-to-id locs)
      (println (merge (d/self-keyed-map bf-min-loc bf-min-cost)
                      {:bf-id (locs-to-id bf-min-loc) :id (hashes-to-id min-point) :cost min-cost})))))

(defn -main []
  (solve))
