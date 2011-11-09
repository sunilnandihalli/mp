(ns try
  (:refer-clojure :exclude [reify inc ==])
  (:use clojure.core.logic)
  (:require [clojure.core.logic.arithmetic :as a]))

(run* [q]
      (fresh [x y]
             (appendo x y [1 2 3 4])
             (== q [x y])))