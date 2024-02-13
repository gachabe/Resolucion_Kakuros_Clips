


;;; NOMBRE: GABRIEL 
;;; APELLIDOS: CHAVES BENÍTEZ


;;; Resolución deductiva de un Kakuro
;;; Departamento de Ciencias de la Computación e Inteligencia Artificial 
;;; Universidad de Sevilla
;;;============================================================================


;;;============================================================================
;;; Representación del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador único de la celda
;;; - fila: Número de fila en la que se encuentra la celda
;;; - columna: Número de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numéricos de 1 a 9.

(deftemplate celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendrá un valor asignado si y solo si dicho
;;; valor es el único elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente función sirve para asignar de forma automática y única
;;; identificadores a las restricciones del puzle. 

(deffunction idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricción tiene los siguientes campos:
;;; - id: Identificador único de la restricción
;;; - valor: Valor de la restricción
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricción

(deftemplate restriccion
  (slot id
        (default-dynamic (idRestriccion)))
  (slot valor)
  (multislot casillas))

;;;============================================================================
;;; Estrategias de resolución
;;;============================================================================

;;;   El objetivo del ejercicio consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.




;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resolución.
;;; La prioridad de estas reglas es -10 para que sean las últimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un único valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el símbolo '?'. El resto de las casillas hasta
;;; completar la cuadrícula 9x9 se dejan en blanco.

(defrule imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

(defrule imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; Funcionalidad para leer los puzles del fichero de ejemplos
;;;============================================================================

;;;   Esta función crea una lista de identificadores de casillas en horizontal.

(deffunction crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))))))
  TRUE)

;;;   Esta función crea una lista de identificadores de casillas en vertical.

(deffunction crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))))))
  TRUE)

;;;   Esta función construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)

;;;   Esta función localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction lee-kakuro (?n)
  (open "ejemplo.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que número de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Qué problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;;   Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))

;;;===========================================================================================================
;;; 			  	SOLUCIÓN
;;;===========================================================================================================
;;; 				PARTICIONES ÚNICAS
;;; Para cierto numeros de celdas existen sumas únicas, por ejemplo, con longitud 2 y restricción 4
;;; sólo puede formarse con 3+1. Por ello se implementa esta plantilla para hacer una primera 
;;; comprobación respecto a nuestras restriccione. Solo veremos algunas de las posibles sumas únicas.
;;; Estas sumas únicas han sido sacadas de https://www.conceptispuzzles.com/index.aspx?uri=puzzle/kakuro/rules

(deftemplate particiones-unicas
	(slot longitud)
	(slot valor)
	(multislot sumas (default (create$ 1 2 3 4 5 6 7 8 9))))

(deffacts sumas-unicas
	(particiones-unicas (longitud 2) (valor 3) (sumas 1 2))
	(particiones-unicas (longitud 2) (valor 4) (sumas 1 3))
	(particiones-unicas (longitud 2) (valor 16) (sumas 7 9))	
	(particiones-unicas (longitud 2) (valor 17) (sumas 8 9))
	(particiones-unicas (longitud 3) (valor 6) (sumas 1 2 3))
	(particiones-unicas (longitud 3) (valor 7) (sumas 1 2 4))
	(particiones-unicas (longitud 3) (valor 23) (sumas 6 8 9))
	(particiones-unicas (longitud 3) (valor 24) (sumas 7 8 9))
	(particiones-unicas (longitud 4) (valor 10) (sumas 1 2 3 4))
	(particiones-unicas (longitud 4) (valor 11) (sumas 1 2 3 5))
	(particiones-unicas (longitud 4) (valor 29) (sumas 5 7 8 9))
	(particiones-unicas (longitud 4) (valor 30) (sumas 6 7 8 9))
	(particiones-unicas (longitud 5) (valor 15) (sumas 1 2 3 4 5))
	(particiones-unicas (longitud 5) (valor 16) (sumas 1 2 3 4 6))
	(particiones-unicas (longitud 5) (valor 34) (sumas 4 6 7 8 9))
	(particiones-unicas (longitud 5) (valor 35) (sumas 5 6 7 8 9))
	(particiones-unicas (longitud 6) (valor 21) (sumas 1 2 3 4 5 6))
	(particiones-unicas (longitud 6) (valor 22) (sumas 1 2 3 4 5 7))
	(particiones-unicas (longitud 6) (valor 38) (sumas 3 5 6 7 8 9))
	(particiones-unicas (longitud 6) (valor 39) (sumas 4 5 6 7 8 9))
	(particiones-unicas (longitud 7) (valor 28) (sumas 1 2 3 4 5 6 7))
	(particiones-unicas (longitud 7) (valor 29) (sumas 1 2 3 4 5 6 8))
	(particiones-unicas (longitud 7) (valor 41) (sumas 2 4 5 6 7 8 9))
	(particiones-unicas (longitud 7) (valor 42) (sumas 3 4 5 6 7 8 9)) 
)		


;;;   Empezaremos creando unas reglas generales, que deberán ser siempre las primeras en
;;; comprobarse debido a su simplicidad y eficiencia para reducir el rango.

;;;============================================================================================================
	

;;; Aqui usaremos la plantilla anteriormente definida comprobando si alguna de las restricciones
;;; es una suma conocida y, para evitar cruce de reglas, comprobaremos que no tenemos aun buena información
;;; sobre la celda que se vaya a actualizar.
(defrule restricciones-sumas-unica
	(declare (salience 97))
	?h1 <- (particiones-unicas (longitud ?l) (valor ?v) (sumas $?r))
	?h2 <- (restriccion (valor ?v) (casillas $?p ?c $?f))
	?h3 <- (celda (id ?c) (rango $?s))	
	(test (= (+ (length$ $?p) (length$ $?f)) (- ?l 1)))
	=>
	(modify ?h3 (rango (intersection$ ?r ?s ))))
 

;;;  Si hay una celda que tiene una unica restriccion, bastaría asignar ese valor al rango.
;;; A esta regla le daremos un alto valor de salience ya que siempre que se pueda debe resolverse una
;;; casilla simple.
(defrule restriccion-con-unica-casilla
  (declare (salience 91))
  ?h1 <- (restriccion (valor ?v) (casillas ?c))
  ?h2 <- (celda (id ?c) (rango $?))
  =>
  (modify ?h2 (rango ?v))
	(retract ?h1))



;;; Aqui intentamos crear nuevas restricciones usando otras restricciones ya conocidas y operando
;;; con sus valores.
;;; Por ejemplo, si tenemos dos restricciones de fila
;;; que afectan a cuatro casillas, una con un valor de 13 y otra de 20, y existe una restriccón
;;; columna que solo afecte a dos de las comunas con valor de 15. Entonces sabemos
;;; que las otras dos casillas columna tienen una restricción de 13+20-15.
;;; Crearemos dos veces la misma regla para trabajar con los dos casos posibles en
;;; pos de la claridad.
(defrule nueva-restriccion1
	?h1 <- (restriccion (valor ?v1) (casillas ?c1 ?c2))
	?h2 <- (restriccion (valor ?v2) (casillas ?c3 ?c4))
	?h3 <- (restriccion (valor ?v3) (casillas ?c1 ?c3))
	(not (restriccion (casillas ?c2 ?c4)))
	(restriccion (valor ?vn) (casillas $?C))
	(test (member$ ?c2 $?C))
	(test (member$ ?c4 $?C))
	=>
	(assert (restriccion (valor (- (+ ?v1 ?v2) ?v3)) (casillas ?c2 ?c4)))
	(assert (restriccion (valor (- ?vn (- (+ ?v1 ?v2) ?v3))) (casillas (difference$ ?C (create$ ?c2 ?c4))))))


(defrule nueva-restriccion2
	?h1 <- (restriccion (valor ?v1) (casillas ?c1 ?c2))
	?h2 <- (restriccion (valor ?v2) (casillas ?c3 ?c4))
	?h3 <- (restriccion (valor ?v3) (casillas ?c2 ?c4))
	(not (restriccion (casillas ?c1 ?c3)))
	(restriccion (valor ?vn) (casillas $?C))
	(test (member$ ?c1 $?C))
	(test (member$ ?c3 $?C))
	=>
	(assert (restriccion (valor (- (+ ?v1 ?v2) ?v3)) (casillas ?c1 ?c3)))
	(assert (restriccion (valor (- ?vn (- (+ ?v1 ?v2) ?v3))) (casillas (difference$ ?C (create$ ?c1 ?c3))))))






;;;  Si en un grupo de celdas para una restriccion ya hay una celda resuelta eliminar 
;;; dicho valor del rango del resto de casillas a las que aplica la misma restricción
;;; puesto que no podemos repetir números.

(defrule eliminar-comunes
	(declare (salience 97))
	?h1 <- (restriccion (valor ?n) (casillas $?i ?c1 $?m ?c2 $?f))
	?h2 <- (celda (id ?c1) (rango ?v))
	?h3 <- (celda (id ?c2) (rango $?ini ?v $?fin))
	=>
	(modify ?h3 (rango $?ini $?fin)))

(defrule eliminar-comunes2
	(declare (salience 97))
	?h1 <- (restriccion (valor ?n) (casillas $?i ?c2 $?m ?c1 $?f))
	?h2 <- (celda (id ?c1) (rango ?v))
	?h3 <- (celda (id ?c2) (rango $?ini ?v $?fin))
	=>
	(modify ?h3 (rango $?ini $?fin)))





;;;  Cada vez que un valor sea colocado actualizaremos las restricciones a las que pertenece
;;; restando el valor colocado y eliminado su celda de las casillas posibles.

(defrule actualiza-restriccion
	?h1 <- (restriccion (valor ?n) (casillas $?i ?c $?f))
	?h2 <- (celda (id ?c) (rango ?v))
	(test (or (> (length$ $?i) 0)  ( > (length$ $?f) 0) ))
	
=>
 (modify ?h1 (valor (- ?n ?v)) (casillas $?i $?f)))



;;;============================================================================
;;; 				      Reglas para 2 celdas
;;;============================================================================

;;; Cuando una restricción afecte a dos casillas y una de las dos está resuelta, 
;;; la solucion de la faltante es  restar la casilla a la restriccion y, el resultado, 
;;; asignarlo a la otra celda. Aunque sea parecida a "actualiza restricción" esta regla
;;; evita posibles pérdidas.
(defrule resolver-2cas
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (rango ?n ))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2)))  (rango $?p ?r1 $?m ?r2 $?f))
  =>
  (modify ?h3
          (rango (- ?v ?n))))


;;;  Cuando una restricción afecte a dos casillas y en el rango de una se encuentra algún valor
;;; tal que la otra casilla no tenga el valor suficiente para sumar la restricción, eliminar esta.

(defrule probar-candidatos-dos-celdas
	(declare (salience 65))
	(restriccion (valor ?v) (casillas ?c1 ?c2))
	?h <- (celda (id ?c&?c1|?c2) (rango $?p ?v1 $?f))
	(or (test (= ?v1 (- ?v ?v1))) 
	(not (celda (id ?c3&~?c&:(or (= ?c3 ?c1) (= ?c3 ?c2)))
	(rango $? =(- ?v ?v1) $?))))
=>
(modify ?h (rango $?p $?f)))

;;;  Dada una restricción que afecte a dos casillas, debido a que no podemos repetir números,
;;; nunca será posible que aparezca la mitad del valor de la restricción en ninguna de las celdas
(defrule mitad-valor-2-casillas
	?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2))
	?h2 <- (celda (id ?c1|?c2) (rango $?r1 =(/ ?v 2) $?r2))
	=>
	(modify ?h2 (rango $?r1 $?r2)))
	


;;;============================================================================
;;; 					     Reglas para 3 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas y no tenemos más información usaremos
;;; fuerza bruta para buscar alguna combinación válida que sea única. Debido
;;; a la tosquedad de esta norma le daremos un bajo salience.

(defrule resolver-3-casillas-fuerza-bruta
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind $?rango3 $?r3)
  (bind $?prueba1 (create$ ) )
  (bind $?prueba2 (create$ ))
  (bind $?prueba3 (create$ ))
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (while (<= ?i (length$ $?rango1)) 
	(bind ?a (nth$ ?i $?rango1))
   (while (<= ?j (length$ $?rango2))
	 (bind ?b (nth$ ?j $?rango2))
    (while (<= ?k (length$ $?rango3)) 
	  (bind ?c (nth$ ?k $?rango3))
  (if (and(= ?v (+ ?a  ?b ?c)) (!= ?a ?b) (!= ?a ?c) (!= ?b ?c))
        then
  	(bind ?prueba1 (union$ $?prueba1 (create$ ?a))) 
  	(bind ?prueba2 (union$ $?prueba2 (create$ ?b))) 
  	(bind ?prueba3 (union$ $?prueba3 (create$ ?c))))
      (bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
      (bind ?i (+ ?i 1))
      (bind ?j 1))
   	(if (and (< (length$ $?prueba1) (length$ ?r1))
   	(< (length$ $?prueba2) (length$ ?r2))
   	(< (length$ $?prueba2) (length$ ?r2)))
	then
   	(modify ?h2 (rango $?prueba1))
   	(modify ?h3 (rango $?prueba2))
   	(modify ?h4 (rango $?prueba3))) )


