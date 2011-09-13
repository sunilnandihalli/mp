(ns mp.core
  (:refer-clojure)
  (:gen-class)
  (:require [mp.debug :as d]
            [clojure.set :as s]
            [clojure.contrib.profile :as p])
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

(defn priority-map-key-by [key-fn comparator & keyvals]
  (priority-map-by #(comparator (key-fn %1) (key-fn %2)) keyvals))


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

(defn abs [a] (if (< a 0) (- a) a))

(defn display [locs-to-id locs]
  (let [[[xmin xmax] [ymin ymax]] (bounding-box locs)]
    (if (< (apply max (map abs [xmin xmax ymin ymax])) 20)
        (let [str (reduce (fn [cstr x]
                            (str cstr (apply str (interpose " " (map #(if-let [i (locs-to-id [x %])] (int-str i) ". ")
                                                                     (range ymin (inc ymax))))) "\n")) "" (range xmin (inc xmax)))]
          (println str)))))

(defn brute-force-solve [locs]
  (let [mcost (fn [[x y]]
                (reduce (fn [cst [xi yi]]
                            (+ cst (max (abs (- x xi)) (abs (- y yi))))) 0 locs))]
    (apply min-key second (map (juxt identity mcost) locs))))

(defn find-nodes-that-enclose-the-unavailable-meeting-point-in-the-vornoi-sense [{:keys [locs] :as whole-problem} [mpx mpy] mp]
  (let [opts (for [x-or-y [:dx :dy] +or- [:+ :-]]
               [x-or-y +or-])
        locs (vec (map (fn [[x y]] [(- x mpx) (- y mpy)]) locs))
        update! (fn update! [tr-mp key f]
                  (let [x (tr-mp key)]
                    (assoc! tr-mp key (f x))))
        cmprtr #(< (second %1) (second %2))
        {:keys [dx+ dx- dy+ dy-]} (reduce (fn [{:keys [dx+ dx- dy+ dy- id] :as w} [x y]]
                                            (thrush-with-pattern [ret] w
                                              (update! ret :id inc)
                                              (if (>= x 0) (update! ret :dx+ #(conj! % [id x])) ret)
                                              (if (<= x 0) (update! ret :dx- #(conj! % [id (- x)])) ret)
                                              (if (>= y 0) (update! ret :dy+ #(conj! % [id y])) ret)
                                              (if (<= y 0) (update! ret :dy- #(conj! % [id (- y)])) ret)))
                                          (transient {:dy+ (transient (vector))
                                                      :dy- (transient (vector))
                                                      :dx+ (transient (vector))
                                                      :dx- (transient (vector)) :id 0}) locs)
        srt (comp (partial sort-by second) persistent!)
        partitions {:dx {:+ (srt dx+) :- (srt dx-)} :dy {:+ (srt dy+) :- (srt dy-)}}
        enclosing-points (fn [[x-or-y +or- :as w]]
                           (let [coord-getter (comp ({:dx first :dy second} x-or-y) locs)
                                 other-direction-coord-getter ({:dx second :dy first} x-or-y)
                                 other-direction-coord-getter-from-id (comp other-direction-coord-getter locs)
                                 ordered-points (get-in partitions [x-or-y +or-])]
                             (loop [pmin nil pmax nil life nil
                                    [[cpid crd :as available] & rest-ord-pts :as all-ord-pts] (seq ordered-points)
                                    vpts-before-min nil vpts-after-max nil]
                               (if-not available (into vpts-after-max vpts-before-min)
                                       (let [s crd cur-crd (locs cpid)]
                                         (if (or (not life) (> life s))
                                           (let [other-crd (other-direction-coord-getter cur-crd)
                                                 {:keys [pmin pmax vpts-after-max vpts-before-min]
                                                  :or {pmin pmin pmax pmax vpts-before-min vpts-before-min
                                                       vpts-after-max vpts-after-max}}
                                                 (cond
                                                  (< other-crd 0) (if (or (not pmin) (< (other-direction-coord-getter pmin) other-crd))
                                                                    {:pmin cur-crd :vpts-before-min (conj vpts-before-min cpid)})
                                                  (> other-crd 0) (if (or (not pmax) (> (other-direction-coord-getter pmax) other-crd))
                                                                    {:pmax cur-crd :vpts-after-max (conj vpts-after-max cpid)})
                                                  (= other-crd 0) {:pmax cur-crd :pmin cur-crd :vpts-before-min (conj vpts-before-min cpid)})
                                                 life (if (and pmin pmax) (abs (- (other-direction-coord-getter pmin) (other-direction-coord-getter pmax))))]
                                             (recur pmin pmax life rest-ord-pts vpts-before-min vpts-after-max))
                                           (into vpts-after-max vpts-before-min)))))))]
    (reduce into #{} (map enclosing-points opts))))

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

(defn corners-of-cost-func [{:keys [locs] :as whole-problem} {:keys [k x+y-coeff x-y-coeff min-x+y max-x+y min-x-y max-x-y] :as w}]
  (let [cost (fn [x+y x-y] (+ k (* x+y-coeff x+y) (* x-y-coeff x-y)))] 
    (for [x+y [min-x+y max-x+y]
          x-y [min-x-y max-x-y]]
      [[x+y x-y] (cost x+y x-y)])))
       
(defn sgn [x] (cond (< x 0) :neg (> x 0) :pos :else :zero))

(let [mx 2e9
      [[lim-x+y-min lim-x+y-max] [lim-x-y-min lim-x-y-max]] [[(- mx) mx] [(- mx) mx]]]     
  (defn cost-fn [whole-problem mp]
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
       :min-x+y  min-x+y :max-x+y max-x+y :min-x-y  min-x-y :max-x-y max-x-y :mp mp})))
       
(defn initial-map-guess [locs n]
  (let [[xsum ysum] (reduce (fn [[xsum ysum] [x y]] [(+ xsum x) (+ ysum y)]) locs)
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
                                                            [dx+ (conj dx- cid) dy+ dy- n-x+y-coll n-x-y-coll ncid]
                                                            [dx+ dx- dy+ (conj dy- cid) n-x+y-coll n-x-y-coll ncid]) 
                                                          (if (< x-y k-x-y)
                                                            [dx+ dx- (conj dy+ cid) dy- n-x+y-coll n-x-y-coll ncid] 
                                                            [(conj dx+ cid) dx- dy+ dy- n-x+y-coll n-x-y-coll ncid]))))
                                                    (conj (vec (repeatedly 6 #(vector-of :int))) 0) locs)
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
        mp {:dx {:+ {:x+y dx+-x+y :x-y dx+-x-y :sum sum-dx+}
                 :- {:x+y dx--x+y :x-y dx--x-y :sum sum-dx-}}
            :dy {:+ {:x+y dy+-x+y :x-y dy+-x-y :sum sum-dy+}
                 :- {:x+y dy--x+y :x-y dy--x-y :sum sum-dy-}}}
        whole-problem {:locs locs :x+y-coll x+y-coll :x-y-coll x-y-coll}]
    [mp whole-problem]))

(defn move [{:keys [locs x+y-coll x-y-coll]} [dir inc-or-dec] mp]
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
        (let [[s1 s2] (map #(get-in ccmp (:from %)) opts)
              [[id1 h1 :as fs1] [id2 h2 :as fs2]] (map (comp peek dir) [s1 s2])]
          (if-let [[[id h] copt] (cond
                                  (and fs1 fs2) (if (inc-or-dec-fn h1 h2) [fs1 opt1] [fs2 opt2])
                                  fs1 [fs1 opt1] fs2 [fs2 opt2])]
            (if-not (or (not old-hash-val) (= old-hash-val h)) ccmp
                    (recur (execute-option ccmp [id copt]) h))
            ccmp))))))

(defn move-to [{:keys [locs x+y-coll x-y-coll] :as whole-problem} mp [x+y x-y]]
  {:post [#_(let [{:keys [min-x+y max-x+y min-x-y max-x-y] :as cfn} (cost-fn whole-problem %)]
              (if-not (and (< min-x+y x+y) (<= x+y max-x+y) (< min-x-y x-y) (<= x-y max-x-y))
                (do (d/d {:ret % :inp (d/self-keyed-map mp x+y x-y)
                          :ret-cfn (d/self-keyed-map min-x+y max-x+y min-x-y max-x-y)}) nil) true))]}
  (let [pt-hash {:x+y x+y :x-y x-y}
        node-mvmt-mp {:x+y [[[:dx :-] [:dy :+]]
                            [[:dy :-] [:dx :+]]]
                      :x-y [[[:dx :-] [:dy :-]]
                            [[:dy :+] [:dx :+]]]}
        execute-option (fn execute-option [cmp {:keys [from to ids] :as opt}]
                         (if-not opt cmp
                                 (let [m-from (get-in cmp from)
                                       m-to (get-in cmp to)
                                       [[dx-or-dy-from] [dx-or-dy-to]] [from to]
                                       [from-coord-getter to-coord-getter] (map {:dx first :dy second} [dx-or-dy-from dx-or-dy-to])
                                       {x+y-set-from :x+y x-y-set-from :x-y sum-from :sum} m-from
                                       {x+y-set-to :x+y x-y-set-to :x-y sum-to :sum} m-to
                                       [x+y-set-from x+y-set-to
                                        x-y-set-from x-y-set-to
                                        sum-from sum-to] (reduce (fn [[x+y-set-from x+y-set-to
                                                                       x-y-set-from x-y-set-to
                                                                       sum-from sum-to] id]
                                                                   (let [loc (locs id)]
                                                                     [(dissoc x+y-set-from id) (assoc x+y-set-to id (x+y-coll id))
                                                                      (dissoc x-y-set-from id) (assoc x-y-set-to id (x-y-coll id))
                                                                      (- sum-from (from-coord-getter loc)) (+ sum-to (to-coord-getter loc))]))
                                                                 [x+y-set-from x+y-set-to
                                                                  x-y-set-from x-y-set-to
                                                                  sum-from sum-to] ids)]
                                   (-> cmp
                                       (assoc-in from (assoc m-from :x+y x+y-set-from :x-y x-y-set-from :sum sum-from))
                                       (assoc-in to (assoc m-to :x+y x+y-set-to :x-y x-y-set-to :sum sum-to))))))
        ensure-in-range (fn ensure-in-range [cmp dir]
                          (let [v (pt-hash dir)
                                opts (node-mvmt-mp dir)
                                helper (fn helper [ccmp [<min >=max]]
                                         (let [<min-set (get-in ccmp (conj <min dir))
                                               >=max-set (get-in ccmp (conj >=max dir))
                                               opt (or (if-let [x (seq (take-while (fn [[_ prty]] (>= prty v)) (seq <min-set)))]
                                                         {:from <min :to >=max :ids (map first x)})
                                                       (if-let [x (seq (take-while (fn [[_ prty]] (< prty v)) (seq >=max-set)))]
                                                         {:from >=max :to <min :ids (map first x)}))]
                                           (execute-option ccmp opt)))]
                            (reduce helper cmp opts)))]
    (reduce ensure-in-range mp [:x+y :x-y])))
                   
(defn dist [[x1 y1] [x2 y2]] (max (abs (- x1 x2)) (abs (- y1 y2))))


(defn brute-force-cost [{:keys [locs]} id]
  (let [[mpx mpy] (locs id)]
    (loop [s 0 [[x y :as loc] & rlocs] locs]
      (if-not loc s
              (let [dx (- x mpx)
                    dy (- y mpy)
                    dx (if (< dx 0) (- dx) dx)
                    dy (if (< dy 0) (- dy) dy)]
                (if (> dx dy) (recur (+ s dx) rlocs) (recur (+ s dy) rlocs)))))))
                    
                    


(defn find-min-cost-among-eff [{:keys [locs x+y-coll x-y-coll] :as whole-problem} pts mp]
    (let [ordered-pts (into (priority-map) (map (juxt identity (juxt x+y-coll x-y-coll)) pts))]
      (peek (second (reduce (fn [[cur-mp cur-pt-cost-pairs] [pid [x+y x-y]]]
                              (let [new-mp (p/prof :move-to (move-to whole-problem cur-mp [x+y x-y]))
                                    {:keys [k x+y-coeff x-y-coeff]} (p/prof :cost-fn-find-min-among-eff (cost-fn whole-problem new-mp))]
                                [new-mp (assoc cur-pt-cost-pairs pid (+ k (* x+y-coeff x+y) (* x-y-coeff x-y)))]))
                            [mp (priority-map)] ordered-pts)))))

(defn find-min-cost-among-bf [{:keys [locs] :as whole-problem} pts _]
  (apply min-key second
         (map (juxt identity
                    (partial brute-force-cost
                             whole-problem)) pts)))

(defn find-min-cost-among [whole-problem pts mp]
  (find-min-cost-among-bf whole-problem pts mp))

(defn optimize [whole-problem mp]
  (loop [{:keys [x+y-coeff x-y-coeff] :as cst-cmp} (cost-fn whole-problem mp) cmp mp [min-xy min-cost] nil]
    (let [[opt1 opt2 :as opts] (filter second [[:x+y (cond
                                                      (> x+y-coeff 0) :dec
                                                      (< x+y-coeff 0) :inc)]
                                               [:x-y (cond
                                                      (> x-y-coeff 0) :dec
                                                      (< x-y-coeff 0) :inc)]])]
      (if-let [mps (seq (keep #(move whole-problem % cmp) opts))]
        (let [[new-cost-fn new-mp [new-min-xy new-min-cost]] (apply min-key (fn [[_ _ [_ x]]] x) 
                                                                    (map (fn [mp]
                                                                           (let [cst-fnc (cost-fn whole-problem mp)
                                                                                 min-corner (apply min-key second (corners-of-cost-func whole-problem cst-fnc))]
                                                                             [cst-fnc mp min-corner])) mps))]
          (if (not (or (not min-cost) (< new-min-cost min-cost))) cmp
              (recur new-cost-fn new-mp [new-min-xy new-min-cost]))) cmp))))

(defn solve-hashing-vornoi-around-mp []
  (let [[n locs] (read-stdin)
        locs (vec (map vec locs))
        [mp {:keys [ locs-to-id hashes-to-id x+y-coll x-y-coll] :as whole-problem}] (initial-map-guess locs n)
        min-mp (optimize whole-problem mp)
        [[xmp ymp :as min-point] min-cost] (apply min-key second (corners-of-cost-func whole-problem (cost-fn whole-problem min-mp)))
        actual-point [(/ (+ xmp ymp) 2) (/ (- xmp ymp) 2)]
        pts (find-nodes-that-enclose-the-unavailable-meeting-point-in-the-vornoi-sense whole-problem actual-point min-mp)]
    (println (second (find-min-cost-among whole-problem pts min-mp)))))

(defn -main [])
  
(defn tt []
  (let [locs (second (read-stdin))]
    (time (solve-hashing-vornoi-around-mp))
    #_(brute-force-solve locs)))






























