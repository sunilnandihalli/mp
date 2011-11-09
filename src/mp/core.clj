(ns mp.core
  (:gen-class)
  
(defn priority-map-key-by [key-fn comparator & keyvals]
  (priority-map-by #(comparator (key-fn %1) (key-fn %2)) keyvals))

(defmacro thrush-with-pattern [[pattern] first & exprs]
  (if (seq exprs) `(let [~pattern ~first] (thrush-with-pattern [~pattern] ~@exprs)) first))

(defn read-stdin [& {:keys [fname] :or {fname "inp.txt"}}]
  (let [vs (or (seq (doall (line-seq (java.io.BufferedReader. *in*))))
               (seq (doall (line-seq (java.io.BufferedReader. (java.io.FileReader. fname))))))
        [[n] & nodes] (->> (map #(re-seq #"[^ ]+" %) vs)
                           (map #(map read-string %)))]
    [n (into [] (take n nodes))]))

(defn abs [a] (if (< a 0) (- a) a))

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
        [dx+ dx- dy+ dy- x+y-coll x-y-coll] (map persistent!
                                                 (take 6 (reduce (fn [[dx+ dx- dy+ dy- x+y-coll x-y-coll cid] [x y]]
                                                                   (let [x+y (+ x y)
                                                                         x-y (- x y)
                                                                         n-x+y-coll (conj! x+y-coll x+y)
                                                                         n-x-y-coll (conj! x-y-coll x-y)
                                                                         ncid (inc cid)]
                                                                     (if (< x+y k-x+y)
                                                                       (if (< x-y k-x-y)
                                                                         [dx+ (conj! dx- cid) dy+ dy- n-x+y-coll n-x-y-coll ncid]
                                                                         [dx+ dx- dy+ (conj! dy- cid) n-x+y-coll n-x-y-coll ncid]) 
                                                                       (if (< x-y k-x-y)
                                                                         [dx+ dx- (conj! dy+ cid) dy- n-x+y-coll n-x-y-coll ncid] 
                                                                         [(conj! dx+ cid) dx- dy+ dy- n-x+y-coll n-x-y-coll ncid]))))
                                                                 (conj (vec (repeatedly 6 #(transient (vector)))) 0) locs)))
        [sum-dx+ sum-dx-] (map #(reduce (fn [s i]
                                          (let [[x _] (locs i)]
                                            (+ s x))) 0 %) [dx+ dx-])
        [sum-dy+ sum-dy-] (map #(reduce (fn [s i]
                                          (let [[_ y] (locs i)]
                                            (+ s y))) 0 %) [dy+ dy-])
        priority-map-creator (fn priority-map-creator [[cmprtr hash-coll coll]]
                               (loop [prty-mp (priority-map-by cmprtr) [cid & rids] (seq coll)]
                                 (if-not cid prty-mp
                                         (recur (assoc prty-mp cid (x+y-coll cid)) rids))))
        [dx+-x+y dx+-x-y dx--x+y dx--x-y dy+-x+y dy+-x-y dy--x+y dy--x-y] (map priority-map-creator [[< x+y-coll dx+]
                                                                                                     [< x-y-coll dx+]
                                                                                                     [> x+y-coll dx-]
                                                                                                     [> x-y-coll dx-]
                                                                                                     [< x+y-coll dy+]
                                                                                                     [> x-y-coll dy+]
                                                                                                     [> x+y-coll dy-]
                                                                                                     [< x-y-coll dy-]])
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

                   
(defn brute-force-cost [{:keys [locs]} id]
  (let [[mpx mpy] (locs id)]
    (loop [s 0 [[x y :as loc] & rlocs] locs]
      (if-not loc s
              (let [dx (- x mpx)
                    dy (- y mpy)
                    dx (if (< dx 0) (- dx) dx)
                    dy (if (< dy 0) (- dy) dy)]
                (if (> dx dy) (recur (+ s dx) rlocs) (recur (+ s dy) rlocs)))))))
                   
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

(defn -main []
  (solve-hashing-vornoi-around-mp))
  





























