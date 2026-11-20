# Printing, reading, equality and metadata

A value of a type prints as a tagged literal, and the tag reads through the type's constructor. So text
never carries proof: a value that is read from text is made by the constructor, which runs
every check for a `rec/defproven` type.

```clojure
(ns library.book
  (:require [clojure.edn :as edn]
            [recognitum.core :as rec]))

(rec/defproven Book [title pages]
  rec/checks
  (title [] "the title is a string" (string? title))
  (pages [] "the page count is positive" (pos-int? pages))

  Object
  (toString [_] (str title ", " pages " pages")))

(def book (map->Book {::title "Emma" ::pages 474}))
```

## Printing

- A sealed value, which is a value of a `rec/defproven` type, prints as `#ns/T {...}`: the type's
  name as the tag, then the map of the entries. A value of a `rec/defproven-in` type prints the
  same way.
- A value of a displaced definition, one that a later definition of its type replaced, prints
  the same way.
- A draft, which is an unchecked map of a type made with `rec/draft`, prints as
  `#recognitum/draft [ns/T {...}]`. No reader reads that form back.
- `str` of a value is its `toString` where the type gives one, and its printed form otherwise.
  Printing with `pr`, `prn` or `pr-str` shows the tagged map either way.

```clojure
(pr-str book)
;; => "#library.book/Book #:library.book{:title \"Emma\", :pages 474}"
(str book)
;; => "Emma, 474 pages"
(pr-str (rec/draft book))
;; => "#recognitum/draft [library.book/Book #:library.book{:title \"Emma\", :pages 474}]"
```

## Reading

The tag `#ns/T` has no reader until the program gives it one. There are two ways:

- **The Clojure reader** (`read`, `read-string`, and literals in source files) takes its
  readers from `data_readers.cljc` on the classpath. One entry maps the tag to the constructor:

  ```text
  {library.book/Book library.book/map->Book}
  ```

- **`clojure.edn`** takes its readers as an option. `(rec/data-readers)` returns a map from the
  tag of each type to its `map->T`, for the types whose names their namespaces map now.

Either way the reader calls `map->T`. For a `rec/defproven` type, reading therefore runs every
check, and text that fails a check throws as the constructor throws. For a `rec/defproven-in`
type, reading checks nothing, as its constructor checks nothing.

```clojure
(def read-back (edn/read-string {:readers (rec/data-readers)} (pr-str book)))

[(= book read-back) (rec/sealed? read-back)]
;; => [true true]
(edn/read-string {:readers (rec/data-readers)}
                 "#library.book/Book #:library.book{:title \"Emma\", :pages 0}")
;; ExceptionInfo: library.book/Book failed 1 check
;;   :library.book/pages (the page count is positive): false
```

A map that `(rec/data-readers)` returned belongs to the definitions that were current when it
was called. After a type is redefined, its entry in an older map throws, and the program calls
`rec/data-readers` again. [redefinition.md](redefinition.md) states the rest.

## Equality and hash

A sealed value equals a plain map of its entries, in both directions, and has that map's hash.
A draft does not equal a plain map of its entries. Two drafts of one type that hold equal
entries are equal.

```clojure
(def entries {::title "Emma" ::pages 474})

[(= book entries) (= entries book) (= (hash book) (hash entries))]
;; => [true true true]
[(= (rec/draft book) entries) (= (rec/draft book) (into (rec/draft Book) entries))]
;; => [false true]
```

So equality says nothing about proof. A plain map that equals a sealed value proves nothing,
and `rec/sealed?` tells the two apart.

## Metadata

A constructor gives the value the metadata of the map it was given, and `rec/seal` gives the
value the metadata of the draft. Printing does not show metadata.

```clojure
(meta (map->Book (with-meta entries {:source "catalog"})))
;; => {:source "catalog"}
```

## Java serialization

A value that is written with Java serialization is written as a plain map of its entries.
Reading the bytes back gives a plain map, which is not sealed.

```clojure
(defn round-trip [x]
  (let [bytes (java.io.ByteArrayOutputStream.)]
    (with-open [out (java.io.ObjectOutputStream. bytes)]
      (.writeObject out x))
    (with-open [in (-> (.toByteArray bytes)
                       (java.io.ByteArrayInputStream.)
                       (java.io.ObjectInputStream.))]
      (.readObject in))))

[(= book (round-trip book)) (rec/sealed? (round-trip book))]
;; => [true false]
```

## Not promised

- That `with-meta` or `vary-meta` on a value returns a sealed value. Code that needs metadata
  on a value puts it on the map or the draft before the value is made.
- What `str` of a draft returns.
- The exact text between the braces of a printed value, which follows Clojure's printer and
  its settings, such as `*print-namespace-maps*`.
