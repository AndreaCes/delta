/*
 * Copyright (2021) The Delta Lake Project Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package io.delta.tables

import scala.collection.JavaConverters._
import scala.collection.Map

import org.apache.spark.sql.delta.util.AnalysisHelper

import org.apache.spark.annotation._
import org.apache.spark.internal.Logging
import org.apache.spark.sql._
import org.apache.spark.sql.catalyst.analysis.UnresolvedAttribute
import org.apache.spark.sql.catalyst.plans.logical._
import org.apache.spark.sql.functions.expr

/**
 * Builder to specify how to merge data from source DataFrame into the target Delta table.
 * You can specify any number of `whenMatched` and `whenNotMatched` clauses.
 * Here are the constraints on these clauses.
 *
 *   - `whenMatched` clauses:
 *
 *     - There can be at most one `update` action and one `delete` action in `whenMatched` clauses.
 *
 *     - Each `whenMatched` clause can have an optional condition. However, if there are two
 *       `whenMatched` clauses, then the first one must have a condition.
 *
 *     - When there are two `whenMatched` clauses and there are conditions (or the lack of)
 *       such that a row matches both clauses, then the first clause/action is executed.
 *       In other words, the order of the `whenMatched` clauses matter.
 *
 *     - If none of the `whenMatched` clauses match a source-target row pair that satisfy
 *       the merge condition, then the target rows will not be updated or deleted.
 *
 *     - If you want to update all the columns of the target Delta table with the
 *       corresponding column of the source DataFrame, then you can use the
 *       `whenMatched(...).updateAll()`. This is equivalent to
 *       <pre>
 *         whenMatched(...).updateExpr(Map(
 *           ("col1", "source.col1"),
 *           ("col2", "source.col2"),
 *           ...))
 *       </pre>
 *
 *   - `whenNotMatched` clauses:
 *
 *     - This clause can have only an `insert` action, which can have an optional condition.
 *
 *     - If the `whenNotMatched` clause is not present or if it is present but the non-matching
 *       source row does not satisfy the condition, then the source row is not inserted.
 *
 *     - If you want to insert all the columns of the target Delta table with the
 *       corresponding column of the source DataFrame, then you can use
 *       `whenMatched(...).insertAll()`. This is equivalent to
 *       <pre>
 *         whenMatched(...).insertExpr(Map(
 *           ("col1", "source.col1"),
 *           ("col2", "source.col2"),
 *           ...))
 *       </pre>
 *
 * Scala example to update a key-value Delta table with new key-values from a source DataFrame:
 * {{{
 *    deltaTable
 *     .as("target")
 *     .merge(
 *       source.as("source"),
 *       "target.key = source.key")
 *     .whenMatched
 *     .updateExpr(Map(
 *       "value" -> "source.value"))
 *     .whenNotMatched
 *     .insertExpr(Map(
 *       "key" -> "source.key",
 *       "value" -> "source.value"))
 *     .execute()
 * }}}
 *
 * Java example to update a key-value Delta table with new key-values from a source DataFrame:
 * {{{
 *    deltaTable
 *     .as("target")
 *     .merge(
 *       source.as("source"),
 *       "target.key = source.key")
 *     .whenMatched
 *     .updateExpr(
 *        new HashMap<String, String>() {{
 *          put("value", "source.value");
 *        }})
 *     .whenNotMatched
 *     .insertExpr(
 *        new HashMap<String, String>() {{
 *         put("key", "source.key");
 *         put("value", "source.value");
 *       }})
 *     .execute();
 * }}}
 *
 * @since 0.3.0
 */
class DeltaMergeBuilder private(
    private val targetTable: DeltaTable,
    private val source: DataFrame,
    private val onCondition: Column,
    private val matchedActions: Seq[MergeAction],
    private val notMatchedActions: Seq[MergeAction])
  extends AnalysisHelper
  with Logging
  {

  /**
   * Build the actions to perform when the merge condition was matched.  This returns
   * [[DeltaMergeMatchedActionBuilder]] object which can be used to specify how
   * to update or delete the matched target table row with the source row.
   * @since 0.3.0
   */
  def whenMatched(): DeltaMergeMatchedActionBuilder = {
    DeltaMergeMatchedActionBuilder(this, None)
  }

  /**
   * Build the actions to perform when the merge condition was matched and
   * the given `condition` is true. This returns [[DeltaMergeMatchedActionBuilder]] object
   * which can be used to specify how to update or delete the matched target table row with the
   * source row.
   *
   * @param condition boolean expression as a SQL formatted string
   * @since 0.3.0
   */
  def whenMatched(condition: String): DeltaMergeMatchedActionBuilder = {
    whenMatched(expr(condition))
  }

  /**
   * Build the actions to perform when the merge condition was matched and
   * the given `condition` is true. This returns a [[DeltaMergeMatchedActionBuilder]] object
   * which can be used to specify how to update or delete the matched target table row with the
   * source row.
   *
   * @param condition boolean expression as a Column object
   * @since 0.3.0
   */
  def whenMatched(condition: Column): DeltaMergeMatchedActionBuilder = {
    DeltaMergeMatchedActionBuilder(this, Some(condition))
  }

  /**
   * Build the action to perform when the merge condition was not matched. This returns
   * [[DeltaMergeNotMatchedActionBuilder]] object which can be used to specify how
   * to insert the new sourced row into the target table.
   * @since 0.3.0
   */
  def whenNotMatched(): DeltaMergeNotMatchedActionBuilder = {
    DeltaMergeNotMatchedActionBuilder(this, None)
  }

  /**
   * Build the actions to perform when the merge condition was not matched and
   * the given `condition` is true. This returns [[DeltaMergeMatchedActionBuilder]] object
   * which can be used to specify how to insert the new sourced row into the target table.
   *
   * @param condition boolean expression as a SQL formatted string
   * @since 0.3.0
   */
  def whenNotMatched(condition: String): DeltaMergeNotMatchedActionBuilder = {
    whenNotMatched(expr(condition))
  }

  /**
   * Build the actions to perform when the merge condition was not matched and
   * the given `condition` is true. This returns [[DeltaMergeMatchedActionBuilder]] object
   * which can be used to specify how to insert the new sourced row into the target table.
   *
   * @param condition boolean expression as a Column object
   * @since 0.3.0
   */
  def whenNotMatched(condition: Column): DeltaMergeNotMatchedActionBuilder = {
    DeltaMergeNotMatchedActionBuilder(this, Some(condition))
  }

  /**
   * Execute the merge operation based on the built matched and not matched actions.
   *
   * @since 0.3.0
   */
  def execute(): Unit = improveUnsupportedOpError {
    val sparkSession = targetTable.toDF.sparkSession

    val targetPlan = targetTable.toDF.queryExecution.analyzed
    val sourcePlan = source.queryExecution.analyzed

    val merge = MergeIntoTable(
      targetPlan,
      sourcePlan,
      onCondition.expr,
      matchedActions,
      notMatchedActions)

    toDataset(sparkSession, merge)
  }

  /**
   * Creates a new DeltaMergeBuilder with the merge matched action in input.
   * The method is meant for internal usage only. Do not call this directly.
   */
  @Unstable
  private[delta] def withMatchedAction(action: MergeAction): DeltaMergeBuilder = {
    new DeltaMergeBuilder(
      this.targetTable,
      this.source,
      this.onCondition,
      this.matchedActions :+ action,
      this.notMatchedActions)
  }

  /**
   * Creates a new DeltaMergeBuilder not matched actions with the action in input.
   * The method is meant for internal usage only. Do not call this directly.
   */
  @Unstable
  private[delta] def withNotMatchedAction(action: MergeAction): DeltaMergeBuilder = {
    new DeltaMergeBuilder(
      this.targetTable,
      this.source,
      this.onCondition,
      this.matchedActions,
      this.notMatchedActions:+ action)
  }
}

object DeltaMergeBuilder {
  /**
   * :: Unstable ::
   *
   * Private method for internal usage only. Do not call this directly.
   */
  @Unstable
  private[delta] def apply(
      targetTable: DeltaTable,
      source: DataFrame,
      onCondition: Column): DeltaMergeBuilder = {
    new DeltaMergeBuilder(targetTable, source, onCondition, Nil, Nil)
  }
}

/**
 * Builder class to specify the actions to perform when a target table row has matched a
 * source row based on the given merge condition and optional match condition.
 *
 * See [[DeltaMergeBuilder]] for more information.
 *
 * @since 0.3.0
 */
class DeltaMergeMatchedActionBuilder private(
    private val mergeBuilder: DeltaMergeBuilder,
    private val matchCondition: Option[Column]) {

  /**
   * Update the matched table rows based on the rules defined by `set`.
   *
   * @param set rules to update a row as a Scala map between target column names and
   *            corresponding update expressions as Column objects.
   * @since 0.3.0
   */
  def update(set: Map[String, Column]): DeltaMergeBuilder = {
    addUpdateClause(set)
  }

  /**
   * Update the matched table rows based on the rules defined by `set`.
   *
   * @param set rules to update a row as a Scala map between target column names and
   *            corresponding update expressions as SQL formatted strings.
   * @since 0.3.0
   */
  def updateExpr(set: Map[String, String]): DeltaMergeBuilder = {
    addUpdateClause(toStrColumnMap(set))
  }

  /**
   * Update a matched table row based on the rules defined by `set`.
   *
   * @param set rules to update a row as a Java map between target column names and
   *            corresponding expressions as Column objects.
   * @since 0.3.0
   */
  def update(set: java.util.Map[String, Column]): DeltaMergeBuilder = {
    addUpdateClause(set.asScala)
  }

  /**
   * Update a matched table row based on the rules defined by `set`.
   *
   * @param set rules to update a row as a Java map between target column names and
   *            corresponding expressions as SQL formatted strings.
   * @since 0.3.0
   */
  def updateExpr(set: java.util.Map[String, String]): DeltaMergeBuilder = {
    addUpdateClause(toStrColumnMap(set.asScala))
  }

  /**
   * Update all the columns of the matched table row with the values of the
   * corresponding columns in the source row.
   * @since 0.3.0
   */
  def updateAll(): DeltaMergeBuilder = {
    val updateAllAction = UpdateStarAction(matchCondition.map(_.expr))
    mergeBuilder.withMatchedAction(updateAllAction)
  }

  /**
   * Delete a matched row from the table.
   * @since 0.3.0
   */
  def delete(): DeltaMergeBuilder = {
    val deleteAction = DeleteAction(matchCondition.map(_.expr))
    mergeBuilder.withMatchedAction(deleteAction)
  }

  private def addUpdateClause(set: Map[String, Column]): DeltaMergeBuilder = {
    if (set.isEmpty && matchCondition.isEmpty) {
      // Nothing to update = no need to add an update clause
      mergeBuilder
    } else {
      val assignments = set.map { case (targetColName, column) =>
        Assignment(UnresolvedAttribute.quotedString(targetColName), column.expr)
      }.toSeq
      val updateAction = UpdateAction(matchCondition.map(_.expr), assignments)
      mergeBuilder.withMatchedAction(updateAction)
    }
  }

  private def toStrColumnMap(map: Map[String, String]): Map[String, Column] = {
    map.toSeq.map { case (k, v) => k -> functions.expr(v) }.toMap
  }
}

object DeltaMergeMatchedActionBuilder {
  /**
   * :: Unstable ::
   *
   * Private method for internal usage only. Do not call this directly.
   */
  @Unstable
  private[delta] def apply(
      mergeBuilder: DeltaMergeBuilder,
      matchCondition: Option[Column]): DeltaMergeMatchedActionBuilder = {
    new DeltaMergeMatchedActionBuilder(mergeBuilder, matchCondition)
  }
}


/**
 * Builder class to specify the actions to perform when a source row has not matched any target
 * Delta table row based on the merge condition, but has matched the additional condition
 * if specified.
 *
 * See [[DeltaMergeBuilder]] for more information.
 *
 * @since 0.3.0
 */
class DeltaMergeNotMatchedActionBuilder private(
    private val mergeBuilder: DeltaMergeBuilder,
    private val notMatchCondition: Option[Column]) {

  /**
   * Insert a new row to the target table based on the rules defined by `values`.
   *
   * @param values rules to insert a row as a Scala map between target column names and
   *               corresponding expressions as Column objects.
   * @since 0.3.0
   */
  def insert(values: Map[String, Column]): DeltaMergeBuilder = {
    addInsertClause(values)
  }

  /**
   * Insert a new row to the target table based on the rules defined by `values`.
   *
   * @param values rules to insert a row as a Scala map between target column names and
   *               corresponding expressions as SQL formatted strings.
   * @since 0.3.0
   */
  def insertExpr(values: Map[String, String]): DeltaMergeBuilder = {
    addInsertClause(toStrColumnMap(values))
  }

  /**
   * Insert a new row to the target table based on the rules defined by `values`.
   *
   * @param values rules to insert a row as a Java map between target column names and
   *               corresponding expressions as Column objects.
   * @since 0.3.0
   */
  def insert(values: java.util.Map[String, Column]): DeltaMergeBuilder = {
    addInsertClause(values.asScala)
  }

  /**
   * Insert a new row to the target table based on the rules defined by `values`.
   *
   * @param values rules to insert a row as a Java map between target column names and
   *               corresponding expressions as SQL formatted strings.
   *
   * @since 0.3.0
   */
  def insertExpr(values: java.util.Map[String, String]): DeltaMergeBuilder = {
    addInsertClause(toStrColumnMap(values.asScala))
  }

  /**
   * Insert a new target Delta table row by assigning the target columns to the values of the
   * corresponding columns in the source row.
   * @since 0.3.0
   */
  def insertAll(): DeltaMergeBuilder = {
    val insertAllAction = InsertStarAction(notMatchCondition.map(_.expr))
    mergeBuilder.withNotMatchedAction(insertAllAction)
  }

  private def addInsertClause(setValues: Map[String, Column]): DeltaMergeBuilder = {
    val assignments = setValues.map { case (targetColName, column) =>
      Assignment(UnresolvedAttribute.quotedString(targetColName), column.expr)
    }.toSeq
    val insertAction = InsertAction(notMatchCondition.map(_.expr), assignments)
    mergeBuilder.withNotMatchedAction(insertAction)
  }

  private def toStrColumnMap(map: Map[String, String]): Map[String, Column] = {
    map.toSeq.map { case (k, v) => k -> functions.expr(v) }.toMap
  }
}

object DeltaMergeNotMatchedActionBuilder {
  /**
   * :: Unstable ::
   *
   * Private method for internal usage only. Do not call this directly.
   */
  @Unstable
  private[delta] def apply(
      mergeBuilder: DeltaMergeBuilder,
      notMatchCondition: Option[Column]): DeltaMergeNotMatchedActionBuilder = {
    new DeltaMergeNotMatchedActionBuilder(mergeBuilder, notMatchCondition)
  }
}
