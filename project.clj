(defproject mp "1.0.0-SNAPSHOT"
  :description "FIXME: write description"
  :dependencies [[org.clojure/clojure "1.3.0"]
                 [org.clojure/algo.generic "0.1.0-SNAPSHOT"]
                 [org.clojure/algo.monads "0.1.1-SNAPSHOT"]
                 [org.clojure/core.incubator "0.1.1-SNAPSHOT"]
                 [org.clojure/core.logic "0.6.6-SNAPSHOT"]
                 [org.clojure/core.match "0.2.0-alpha7-SNAPSHOT"]
                 [org.clojure/core.unify "0.5.2-SNAPSHOT"]
                 [org.clojure/data.codec "0.1.1-SNAPSHOT"]
                 [org.clojure/data.csv "0.1.1-SNAPSHOT"]
                 [org.clojure/data.finger-tree "0.0.2-SNAPSHOT"]
                 [org.clojure/data.json "0.1.3-SNAPSHOT"]
                 [org.clojure/data.priority-map "0.0.1"]
                 [org.clojure/data.zip "0.1.1-SNAPSHOT"]
                 [org.clojure/math.combinatorics "0.0.3-SNAPSHOT"]
                 [org.clojure/math.numeric-tower "0.0.2-SNAPSHOT"]
                 [org.clojure/test.generative "0.1.4-SNAPSHOT"]
                 [org.clojure/tools.cli "0.2.2-SNAPSHOT"]
                 [org.clojure/tools.logging "0.2.4-SNAPSHOT"]
                 [org.clojure/tools.macro "0.1.2-SNAPSHOT"]
                 [org.clojure/tools.namespace "0.1.2-SNAPSHOT"]
                 [org.clojure/tools.nrepl "0.0.6-SNAPSHOT"]
                 [org.clojure/tools.trace "0.7.1"]]
  :repositories {"sonatype-oss-public"
                 "https://oss.sonatype.org/content/groups/public/"}
  :dev-dependencies [[swank-clojure "1.4.0-SNAPSHOT"]]
  :main mp.core)
  