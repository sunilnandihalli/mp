(ns mp.core
  (:refer-clojure)
  (:gen-class)
  (:require [mp.debug :as d])
  (:import clojure.lang.MapEntry java.util.Map clojure.lang.PersistentTreeMap
           (clojure.lang Seqable Sequential ISeq IPersistentSet ILookup
                         IPersistentStack IPersistentCollection Associative
                         Sorted Reversible Indexed Counted)))

(defprotocol ConjL
  (conjl [s a] "Append a to the left-hand side of s"))

(defprotocol ObjMeter
  "Object for annotating tree elements.  idElem and op together form a Monoid."
  (measure [_ o] "Return the measured value of o (same type as idElem)")
  (idElem [_] "Return the identity element for this meter")
  (opfn [_] "Return an associative function of two args for combining measures"))

(defprotocol Measured
  (measured [o] "Return the measured value of o")
  (getMeter [o] "Return the meter object for o"))

(defprotocol Splittable
  (split [o pred acc] "Return [pre m post] where pre and post are trees"))

(defprotocol SplitAt
  (ft-split-at [o k notfound] [o k]
               "Return [pre m post] where pre and post are trees"))

(defprotocol Tree
  (app3 [t1 ts t2] "Append ts and (possibly deep) t2 to tree t1")
  (app3deep [t2 ts t1] "Append ts and t2 to deep tree t1")
  (measureMore [o] "Return the measure of o not including the leftmost item")
  (measurePop [o] "Return the measure of o not including the rightmost item"))

(extend-type nil
  ObjMeter
  (measure [_ _] nil)
  (idElem [_] nil)
  (opfn [_] nil)
  Measured
  (measured [_] nil)
  (getMeter [_] nil))

(declare newEmptyTree newSingleTree newDeepTree digit deep)

(defmacro ^:private defdigit [& items]
  (let [i (gensym "i_")
        p (gensym "p_")
        o (gensym "o_")
        typename (symbol (str "Digit" (count items)))
        this-items (map #(list (keyword %) o) items)]
   `(deftype ~typename [~@items ~'meter-obj ~'measure-ref]
      Seqable
        (seq [_] ~(reduce #(list `cons %2 %1) nil (reverse items)))
      Indexed
        (count [_] ~(count items)) ; not needed?
        (nth [_ ~i notfound#]
          (cond ~@(mapcat (fn [sym n] [`(== ~i (int ~n)) sym])
                          items
                          (range (count items)))
            :else notfound#))
      Sequential
      ISeq
        (first     [_] ~(first items))
        (more      [_] ~(if (> (count items) 1)
                          `(digit ~'meter-obj ~@(next items))
                          `(newEmptyTree ~'meter-obj)))
        (next      [_] ~(when (> (count items) 1)
                          `(digit ~'meter-obj ~@(next items))))
      IPersistentStack
        (peek      [_] ~(last items))
        (pop       [_] ~(if (> (count items) 1)
                          `(digit ~'meter-obj ~@(drop-last items))
                          `(newEmptyTree ~'meter-obj)))
      IPersistentCollection
        (empty [_]) ; TBD ; not needed?
        (equiv [_ x] false) ; TBD
        (cons  [_ x#] (digit ~'meter-obj ~@items x#))
      ConjL
        (conjl [_ x#] (digit ~'meter-obj x# ~@items))
      Measured
        (measured [_] @~'measure-ref)
        (getMeter [_] ~'meter-obj) ; not needed?
      Splittable ; allow to fail if op is nil:
        (split [_ ~p ~i]
          ~(letfn [(step [ips [ix & ixs]]
                      (if (empty? ixs)
                        [(when ips `(digit ~'meter-obj ~@ips))
                         ix
                         nil]
                        `(let [~i ((opfn ~'meter-obj)
                                     ~i
                                     (measure ~'meter-obj ~ix))]
                           (if (~p ~i)
                             [~(when ips
                                 `(digit ~'meter-obj ~@ips))
                              ~ix
                              (digit ~'meter-obj ~@ixs)]
                             ~(step (concat ips [ix]) ixs)))))]
             (step nil items))))))

(defmacro ^:private make-digit [meter-obj & items]
  (let [typename (symbol (str "Digit" (count items)))]
    `(let [~'mobj ~meter-obj
           ~'op (opfn ~'mobj)]
       (new ~typename ~@items ~'mobj
            (when ~'op
              (delay ~(reduce #(list 'op %1 %2)
                              (map #(list `measure 'mobj %) items))))))))

(defmacro meter [measure idElem op]
  `(reify ObjMeter
      (measure [_ a#] (~measure a#))
      (idElem [_] ~idElem)
      (opfn [_] ~op)))

(defdigit a)
(defdigit a b)
(defdigit a b c)
(defdigit a b c d)

;; cannot be static because it calls protocol methods
(defn digit
  ([meter-obj a]       (make-digit meter-obj a))
  ([meter-obj a b]     (make-digit meter-obj a b))
  ([meter-obj a b c]   (make-digit meter-obj a b c))
  ([meter-obj a b c d] (make-digit meter-obj a b c d)))

(defn ^:static nodes [mfns xs]
  (let [v (vec xs), c (count v)]
    (seq
      (loop [i (int 0), nds []]
        (condp == (- c i)
          (int 2) (-> nds (conj (digit mfns (v i) (v (+ (int 1) i)))))
          (int 3) (-> nds (conj (digit mfns (v i) (v (+ (int 1) i))
                                       (v (+ (int 2) i)))))
          (int 4) (-> nds (conj (digit mfns (v i) (v (+ (int 1) i))))
                    (conj (digit mfns (v (+ (int 2) i))
                                 (v (+ (int 3) i)))))
          (recur (+ (int 3) i)
                 (-> nds
                   (conj (digit mfns (v i) (v (+ (int 1) i))
                                (v (+ (int 2) i)))))))))))

(deftype EmptyTree [meter-obj]
  Seqable
    (seq [_] nil)
  Sequential
  ISeq
    (first [_] nil)
    (more [this] this)
    (next [_] nil)
  IPersistentStack
    (peek [_] nil)
    (pop [this] this)
  Reversible
    (rseq [_] nil)
  IPersistentCollection
    (count [_] 0) ; not needed?
    (empty [this] this)
    (equiv [_ x] false) ; TBD
    (cons  [_ b] (newSingleTree meter-obj b))
  ConjL
    (conjl [_ a] (newSingleTree meter-obj a))
  Measured
    (measured [_] (idElem meter-obj))
    (getMeter [_] meter-obj) ; not needed?
;  Splittable
;    (split [pred acc]) ; TBD -- not needed??
  Tree
    (app3 [_ ts t2] (reduce conjl t2 (reverse ts)))
    (app3deep [_ ts t1] (reduce conj t1 ts))
    (measureMore [_] (idElem meter-obj))
    (measurePop [_] (idElem meter-obj)))

(defn ^:static newEmptyTree [meter-obj]
  (EmptyTree. meter-obj))

(defn ^:static finger-meter [meter-obj]
  (when meter-obj
    (meter
      #(measured %)
      (idElem meter-obj)
      (opfn meter-obj))))

(deftype SingleTree [meter-obj x]
  Seqable
    (seq [this] this)
  Sequential
  ISeq
    (first [_] x)
    (more [_] (EmptyTree. meter-obj))
    (next [_] nil)
  IPersistentStack
    (peek [_] x)
    (pop [_] (EmptyTree. meter-obj))
  Reversible
    (rseq [_] (list x)) ; not 'this' because tree ops can't be reversed
  IPersistentCollection
    (count [_]) ; not needed?
    (empty [_] (EmptyTree. meter-obj)) ; not needed?
    (equiv [_ x] false) ; TBD
    (cons  [_ b] (deep (digit meter-obj x)
                       (EmptyTree. (finger-meter meter-obj))
                       (digit meter-obj b)))
  ConjL
    (conjl [_ a] (deep (digit meter-obj a)
                       (EmptyTree. (finger-meter meter-obj))
                       (digit meter-obj x)))
  Measured
    (measured [_] (measure meter-obj x))
    (getMeter [_] meter-obj) ; not needed?
  Splittable
    (split [this pred acc] (let [e (empty this)] [e x e]))
  Tree
    (app3 [this ts t2] (conjl (app3 (empty this) ts t2) x))
    (app3deep [_ ts t1] (conj (reduce conj t1 ts) x))
    (measureMore [_] (idElem meter-obj))
    (measurePop [_] (idElem meter-obj)))

(defn ^:static newSingleTree [meter-obj x]
  (SingleTree. meter-obj x))

(deftype DelayedTree [tree-ref mval]
  Seqable
    (seq [this] this)
  Sequential
  ISeq
    (first [_] (first @tree-ref))
    (more [_] (rest @tree-ref))
    (next [_] (next @tree-ref))
  IPersistentStack
    (peek [_] (peek @tree-ref))
    (pop [_] (pop @tree-ref))
  Reversible
    (rseq [_] (rseq @tree-ref)) ; not this because tree ops can't be reversed
  IPersistentCollection
    (count [_]) ; not needed?
    (empty [_] (empty @tree-ref))
    (equiv [_ x] false) ; TBD
    (cons  [_ b] (conj @tree-ref b))
  ConjL
    (conjl [_ a] (conjl @tree-ref a))
  Measured
    (measured [_] mval)
    (getMeter [_] (getMeter @tree-ref)) ; not needed?
  Splittable
    (split [_ pred acc] (split @tree-ref pred acc))
  Tree
    (app3 [_ ts t2] (app3 @tree-ref ts t2))
    (app3deep [_ ts t1] (app3deep @tree-ref ts t1))
    (measureMore [_] (measureMore @tree-ref))
    (measurePop [_] (measurePop @tree-ref)))

(defmacro ^:private delay-ft [tree-expr mval]
  `(DelayedTree. (delay ~tree-expr) ~mval))
  ;`(let [v# ~mval] (assert v#) ~tree-expr))
  ;`(delayed-ft (delay (do (print "\nforce ") ~tree-expr)) ~mval))

(defn ^:static to-tree [meter-obj coll]
  (reduce conj (EmptyTree. meter-obj) coll))

(defn deep-left [pre m suf]
  (cond
    (seq pre) (deep pre m suf)
    (empty? (first m)) (to-tree (getMeter suf) suf)
    :else (deep (first m)
                (delay-ft (rest m) (measureMore m))
                suf)))

(defn deep-right [pre m suf]
  (cond
    (seq suf) (deep pre m suf)
    (empty? (peek m)) (to-tree (getMeter pre) pre)
    :else (deep pre
                (delay-ft (pop m) (measurePop m))
                (peek m))))

(defn ^:private measured3 [meter-obj pre m suf]
  (when-let [op (opfn meter-obj)]
    (op
      (op (measured pre)
          (measured m))
        (measured suf))))

(defn deep [pre m suf]
  (let [meter-obj (getMeter pre)
        op (opfn meter-obj)]
    (newDeepTree meter-obj pre m suf
                 (when op
                   (delay (if (seq m)
                            (measured3 meter-obj pre m suf)
                            (op (measured pre) (measured suf))))))))

(deftype DeepTree [meter-obj pre mid suf mval]
  Seqable
    (seq [this] this)
  Sequential
  ISeq
    (first [_] (first pre))
    (more [_] (deep-left (rest pre) mid suf))
    (next [this] (seq (rest this)))
  IPersistentStack
    (peek [_] (peek suf))
    (pop [_] (deep-right pre mid (pop suf)))
  Reversible
    (rseq [this] (lazy-seq (cons (peek this) (rseq (pop this)))))
  IPersistentCollection
    (count [_]) ; not needed?
    (empty [_] (newEmptyTree meter-obj))
    (equiv [_ x] false) ; TBD
    (cons  [_ a] (if (< (count suf) 4)
                   (deep pre mid (conj suf a))
                   (let [[e d c b] suf
                         n (digit meter-obj e d c)]
                     (deep pre (conj mid n) (digit meter-obj b a)))))
  ConjL
    (conjl [_ a] (if (< (count pre) 4)
                   (deep (conjl pre a) mid suf)
                   (let [[b c d e] pre
                         n (digit meter-obj c d e)]
                     (deep (digit meter-obj a b) (conjl mid n) suf))))
  Measured
    (measured [_] @mval)
    (getMeter [_] (getMeter pre)) ; not needed?
  Splittable ; allow to fail if op is nil:
    (split [_ pred acc]
      (let [op (opfn meter-obj)
            vpr (op acc (measured pre))]
        (if (pred vpr)
          (let [[sl sx sr] (split pre pred acc)]
            [(to-tree meter-obj sl) sx (deep-left sr mid suf)])
          (let [vm (op vpr (measured mid))]
            (if (pred vm)
              (let [[ml xs mr] (split mid pred vpr)
                    [sl sx sr] (split xs pred (op vpr (measured ml)))]
                [(deep-right pre ml sl) sx (deep-left sr mr suf)])
              (let [[sl sx sr] (split suf pred vm)]
                [(deep-right pre mid sl)
                  sx
                  (to-tree meter-obj sr)]))))))
  Tree
    (app3 [this ts t2] (app3deep t2 ts this))
    (app3deep [_ ts t1]
      (deep (.pre ^DeepTree t1)
            (app3 (.mid ^DeepTree t1)
                  (nodes meter-obj (concat (.suf ^DeepTree t1) ts pre))
                  mid)
            suf))
    (measureMore [this] (measured3 meter-obj (rest pre) mid suf))
    (measurePop  [this] (measured3 meter-obj pre mid (pop suf))))

(defn ^:static newDeepTree [meter-obj pre mid suf mval]
  (DeepTree. meter-obj pre mid suf mval))

(defn ^:static finger-tree [meter-obj & xs]
  (to-tree meter-obj xs))

(defn split-tree [t p]
  (split t p (idElem (getMeter t))))

(defn ft-concat [t1 t2]
  (assert (= (getMeter t1) (getMeter t2))) ;meters must be the same
  (app3 t1 nil t2))

(defn- seq-equals [a b]
  (boolean
    (when (or (sequential? b) (instance? java.util.List b))
      (loop [a (seq a), b (seq b)]
        (when (= (nil? a) (nil? b))
          (or
            (nil? a)
            (when (= (first a) (first b))
              (recur (next a) (next b)))))))))

;;=== applications ===

(deftype DoubleList [tree mdata]
  Object
    (equals [_ x] (seq-equals tree x))
    (hashCode [this] (hash (map identity this)))
  clojure.lang.IObj
    (meta [_] mdata)
    (withMeta [_ mdata] (DoubleList. tree mdata))
  Sequential
  Seqable
    (seq [this] (when (seq tree) this))
  ISeq
    (first [_] (first tree))
    (more [_] (DoubleList. (rest tree) mdata))
    (next [_] (if-let [t (next tree)] (DoubleList. t mdata)))
  IPersistentStack ; actually, queue
    (peek [_] (peek tree))
    (pop [_] (DoubleList. (pop tree) mdata))
  Reversible
    (rseq [_] (rseq tree)) ; not 'this' because tree ops can't be reversed
  IPersistentCollection
    (count [_] (count (seq tree))) ; Slow!
    (empty [_] (DoubleList. (empty tree) mdata))
    (equiv [_ x] (seq-equals tree x))
    (cons  [_ b] (DoubleList. (conj tree b) mdata))
  ConjL
    (conjl [_ a] (DoubleList. (conjl tree a) mdata))
  Measured
    (measured [_] (measured tree))
    (getMeter [_] (getMeter tree))
  Tree
    (app3 [_ ts t2] (DoubleList. (app3 tree ts t2) mdata))
    (app3deep [_ ts t1] (DoubleList. (app3deep tree ts t1) mdata)))

(defn double-list [& args]
  (into (DoubleList. (EmptyTree. nil) nil) args))

(deftype CountedDoubleList [tree mdata]
  Object
    (equals [_ x] (seq-equals tree x))
    (hashCode [this] (hash (map identity this)))
  clojure.lang.IObj
    (meta [_] mdata)
    (withMeta [_ mdata] (CountedDoubleList. tree mdata))
  Sequential
  Seqable
    (seq [this] (when (seq tree) this))
  ISeq
    (first [_] (first tree))
    (more [_] (CountedDoubleList. (rest tree) mdata))
    (next [_] (if-let [t (next tree)] (CountedDoubleList. t mdata)))
  IPersistentStack
    (peek [_] (peek tree))
    (pop [_] (CountedDoubleList. (pop tree) mdata))
  Reversible
    (rseq [_] (rseq tree)) ; not 'this' because tree ops can't be reversed
  IPersistentCollection
    (empty [_] (CountedDoubleList. (empty tree) mdata))
    (equiv [_ x] (seq-equals tree x))
    (cons  [_ b] (CountedDoubleList. (conj tree b) mdata))
  ConjL
    (conjl [_ a] (CountedDoubleList. (conjl tree a) mdata))
  Measured
    (measured [_] (measured tree))
    (getMeter [_] (getMeter tree)) ; not needed?
  SplitAt
    (ft-split-at [this n notfound]
      (cond
        (< n 0) [(empty this) notfound this]
        (< n (count this))
          (let [[pre m post] (split-tree tree #(> % n))]
            [(CountedDoubleList. pre mdata) m (CountedDoubleList. post mdata)])
        :else [this notfound (empty this)]))
    (ft-split-at [this n]
      (ft-split-at this n nil))
  Tree
    (app3 [_ ts t2]
      (CountedDoubleList. (app3 tree ts (.tree ^CountedDoubleList t2)) mdata))
    ;(app3deep [_ ts t1] (CountedDoubleList. (app3deep tree ts t1) mdata))
    (measureMore [_] (measureMore tree))
    (measurePop [_] (measurePop tree))
  Counted
    (count [_] (measured tree))
  Associative
    (assoc [this k v]
      (cond
        (== k -1) (conjl this v)
        (== k (measured tree)) (conj this v)
        (< -1 k (measured tree))
          (let [[pre mid post] (split-tree tree #(> % k))]
            (CountedDoubleList. (ft-concat (conj pre v) post) mdata))
        :else (throw (IndexOutOfBoundsException.))))
    (containsKey [_ k] (< -1 k (measured tree)))
    (entryAt [_ n] (clojure.lang.MapEntry.
                     n (second (split-tree tree #(> % n)))))
    (valAt [this n notfound] (if (.containsKey this n)
                               (second (split-tree tree #(> % n)))
                               notfound))
    (valAt [this n] (.valAt this n nil))
  Indexed
    (nth [this n notfound] (if (.containsKey this n)
                             (second (split-tree tree #(> % n)))
                             notfound))
    (nth [this n] (if (.containsKey this n)
                    (second (split-tree tree #(> % n)))
                    (throw (IndexOutOfBoundsException.)))))

(let [measure-len (constantly 1)
      len-meter (meter measure-len 0 +)]
  (def empty-counted-double-list
    (CountedDoubleList. (EmptyTree. len-meter) nil)))

(defn counted-double-list [& args]
  (into empty-counted-double-list args))


(defrecord Len-Right-Meter [^int len right])

(def ^:private notfound (Object.))

(deftype CountedSortedSet [cmpr tree mdata]
  Object
    (equals [_ x]
      (boolean
        (if (instance? java.util.Set x)
          (and (= (count x) (count tree)) 
               (every? #(contains? x %) tree))
          (seq-equals tree x))))
    (hashCode [_] (reduce + (map hash tree)))
  clojure.lang.IObj
    (meta [_] mdata)
    (withMeta [_ mdata] (CountedSortedSet. cmpr tree mdata))
  Seqable
    ; return 'tree' instead of 'this' so that result will be Sequential
    (seq [this] (when (seq tree) tree))
  IPersistentCollection
    (cons [this value]
      (if (empty? tree)
        (CountedSortedSet. cmpr (conj tree value) mdata)
        (let [[l x r] (split-tree tree #(>= 0 (cmpr value (:right %))))
              compared (cmpr value x)]
          (if (zero? compared)
            this ; already in set
            (let [[a b] (if (>= 0 compared) [value x] [x value])]
              (CountedSortedSet. cmpr (ft-concat (conj l a) (conjl r b)) mdata))))))
    (empty [_] (CountedSortedSet. cmpr (empty tree) mdata))
    (equiv [this x] (.equals this x)) ; TBD
  ISeq
    (first [_] (first tree))
    (more [_] (CountedSortedSet. cmpr (rest tree) mdata))
    (next [_] (if-let [t (next tree)] (CountedSortedSet. cmpr t mdata)))
  IPersistentStack
    (peek [_] (peek tree))
    (pop [_] (CountedSortedSet. cmpr (pop tree) mdata))
  Reversible
    (rseq [_] (rseq tree)) ; not 'this' because tree ops can't be reversed
  Measured
    (measured [_] (measured tree))
    (getMeter [_] (getMeter tree)) ; not needed?
  SplitAt
    (ft-split-at [this n notfound]
      (cond
        (< n 0) [(empty this) notfound this]
        (< n (count this)) (let [[l x r] (split-tree tree #(> (:len %) n))]
                             [(CountedSortedSet. cmpr l mdata) x
                              (CountedSortedSet. cmpr r mdata)])
        :else [this notfound (empty this)]))
    (ft-split-at [this n]
      (ft-split-at this n nil))
  Counted
    (count [_] (:len (measured tree)))
  ILookup
    (valAt [_ k notfound]
      (if (empty? tree)
        notfound
        (let [x (second (split-tree tree #(>= 0 (cmpr k (:right %)))))]
          (if (= x k)
            k
            notfound))))
    (valAt [this k]
      (.valAt this k nil))
  IPersistentSet
    (disjoin [this k]
      (if (empty? tree)
        this
        (let [[l x r] (split-tree tree #(>= 0 (cmpr k (:right %))))]
          (if (= x k)
            (CountedSortedSet. cmpr (ft-concat l r) mdata)
            this))))
    (get [this k] (.valAt this k nil))
  Indexed
    (nth [this n notfound] (if (< -1 n (:len (measured tree)))
                             (second (split-tree tree #(> (:len %) n)))
                             notfound))
    (nth [this n] (if (< -1 n (:len (measured tree)))
                    (second (split-tree tree #(> (:len %) n)))
                    (throw (IndexOutOfBoundsException.))))
  Sorted
    (comparator [_] cmpr)
    (entryKey [_ x] x)
    (seq [this ascending?] (if ascending?  (.seq this) (rseq tree)))
    (seqFrom [_ k ascending?]
      (let [[l x r] (split-tree tree #(>= 0 (cmpr k (:right %))))]
        (if ascending?
          (CountedSortedSet. cmpr (conjl r x) mdata)
          (rseq (conj l x)))))
  java.util.Set
    (contains [this x] (not= notfound (get this x notfound)))
    (containsAll [this xs] (every? #(contains? this %) xs))
    (isEmpty [_] (empty? tree))
    (iterator [_]
      (let [t (atom tree)]
        (reify java.util.Iterator
          (next [_] (first (swap! t next))) 
          (hasNext [_] (boolean (next @t))))))
    (size [this] (count this))
    (toArray [_] nil) ; TBD
    (toArray [_ a] nil)) ; TBD



(let [measure-lr (fn [x] (Len-Right-Meter. 1 x))
      zero-lr (Len-Right-Meter. 0 nil)
      len-lr (meter measure-lr
                    zero-lr
                    #(Len-Right-Meter. (+ (.len ^Len-Right-Meter %1)
                                          (.len ^Len-Right-Meter %2))
                                       (or (:right %2) (:right %1))))
      empty-tree (EmptyTree. len-lr)
      default-empty-set (CountedSortedSet. compare empty-tree nil)]
  (defn counted-sorted-set-by [cmpr & args]
    (into (CountedSortedSet. cmpr empty-tree nil) args))
  (defn counted-sorted-set [& args]
    (into default-empty-set args)))

;(prefer-method clojure.pprint/simple-dispatch IPersistentSet ISeq)

(defprotocol PrintableTree
  (print-tree [tree]))

(defn- p [t & xs]
  (print "<")
  (print t)
  (doseq [x xs]
    (print " ")
    (print-tree x))
  (print ">"))

(extend-protocol PrintableTree
  Digit1      (print-tree [x] (p "Digit1" (.a x)))
  Digit2      (print-tree [x] (p "Digit2" (.a x) (.b x)))
  Digit3      (print-tree [x] (p "Digit3" (.a x) (.b x) (.c x)))
  Digit4      (print-tree [x] (p "Digit4" (.a x) (.b x) (.c x) (.d x)))
  EmptyTree   (print-tree [x] (p "EmptyTree"))
  DelayedTree (print-tree [x] (p "DelayedTree" @(.tree-ref x)))
  DeepTree    (print-tree [x] (p "DeepTree" (.pre x) (.mid x) (.suf x)))
  SingleTree  (print-tree [x] (p "SingleTree" (.x x)))
  Object      (print-tree [x] (pr x)))



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
        add-node (fn add-node [w [cx cy :as np]]
                   {:pre [#_(clojure.inspector/inspect-tree w)]}
                   (let [new-node-id (locs-to-id np)]
                     (thrush-with-pattern [{:keys [front pfront graph-edges] :as w}]
                       (loop [{ge :graph-edges f :front pf :pfront} w]
                         (let [[cid s-max] (peek pf)]
                           (if-not (>= cx s-max) w
                                   (let [[x0 y0] (locs cid)
                                         [p-1 p-2] (map second (rsubseq f < y0))
                                         [p+1 p+2] (map second (subseq f > y0))
                                         [[x-2 y-2] [x-1 y-1] [x+1 y+1] [x+2 y+2]] (map #(when % (locs %)) [p-2 p-1 p+1 p+2])
                                         new-f (dissoc f y0)
                                         new-pf (thrush-with-pattern [x]
                                                  (pop pf)
                                                  (if-not p-1 x
                                                          (assoc x p-1 (cond
                                                                        (and p-2 p+1) (+ x-1 (- y+1 y-2))
                                                                        p+1 (+ (* 2 (- y+1 ymin)) x-1)
                                                                        p-2 (+ (* 2 (- ymax y-2)) x-1)
                                                                        :else xmax)))
                                                  (if-not p+1 x
                                                          (assoc x p+1 (cond
                                                                        (and p-1 p+2) (+ x+1 (- y+2 y-1))
                                                                        p-1 (+ (* 2 (- ymax y-1)) x+1)
                                                                        p+2 (+ (* 2 (- y+2 ymin)) x+1)
                                                                        :else xmax))))
                                         new-ge (if (and p-1 p+1) (conj ge [p-1 p+1]) ge)]
                                     (recur {:graph-edges new-ge :front new-f :pfront new-pf})))))
                       (let [[new-pf new-ge] (if-let [old-same-y-node-id (front cy)]
                                               [(dissoc pfront old-same-y-node-id)
                                                (conj graph-edges [old-same-y-node-id new-node-id])]
                                               [pfront graph-edges])]
                         {:graph-edges new-ge :front front :pfront new-pf})
                       (let [new-f (assoc front cy new-node-id)
                             [p-1 p-2] (map second (rsubseq new-f < cy))
                             [p+1 p+2] (map second (subseq new-f > cy))
                             [[x-2 y-2] [x-1 y-1] [x+1 y+1] [x+2 y+2]] (map #(when % (locs %)) [p-2 p-1 p+1 p+2])
                             new-pf (thrush-with-pattern [x]
                                      (assoc pfront new-node-id (cond
                                                                 (and p-1 p+1) (+ cx (- y+1 y-1))
                                                                 p+1 (+ (* 2 (- y+1 ymin)) cx)
                                                                 p-1 (+ (* 2 (- ymax y-1)) cx)
                                                                 :else xmax))
                                      (if-not p+1 x
                                              (assoc x p+1 (cond
                                                            p+2 (+ cx (- y+2 y-1))
                                                            :else (+ (* 2 (- ymax cy)) cx))))
                                      (if-not p-1 x
                                              (assoc x p-1 (cond
                                                            p-2 (+ cx (- ymax y-2))
                                                            :else (+ (* 2 (- cy ymin)) cx)))))
                             new-ge (thrush-with-pattern [x]
                                      (if p+1 (conj graph-edges [new-node-id p+1]) graph-edges)
                                      (if p-1 (conj x [new-node-id p-1]) x))]
                         {:graph-edges new-ge :front new-f :pfront new-pf}))))
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
