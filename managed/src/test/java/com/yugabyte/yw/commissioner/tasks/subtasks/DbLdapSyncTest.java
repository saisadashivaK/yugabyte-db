package com.yugabyte.yw.commissioner.tasks.subtasks;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.yugabyte.yw.commissioner.tasks.CommissionerBaseTest;
import com.yugabyte.yw.commissioner.tasks.LdapUnivSync;
import com.yugabyte.yw.commissioner.tasks.subtasks.ldapsync.DbLdapSync;
import com.yugabyte.yw.common.ModelFactory;
import com.yugabyte.yw.models.Customer;
import com.yugabyte.yw.models.Universe;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.junit.MockitoJUnitRunner;

@RunWith(MockitoJUnitRunner.class)
public class DbLdapSyncTest extends CommissionerBaseTest {

  private Customer defaultCustomer;
  private Universe defaultUniverse;

  private LdapUnivSync.Params params;
  private DbLdapSync task;

  private List<String> dbStateSuperusers = new ArrayList<>();
  private HashMap<String, List<String>> dbStateUsers = new HashMap<>();
  private HashMap<String, List<String>> userToGroup = new HashMap<>();
  private List<String> ldapGroups = new ArrayList<>();

  @Before
  public void setUp() {
    super.setUp();
    defaultCustomer = ModelFactory.testCustomer();
    defaultUniverse = ModelFactory.createUniverse(defaultCustomer.getId());
    defaultUniverse = ModelFactory.addNodesToUniverse(defaultUniverse.getUniverseUUID(), 1);

    // Setup Ldap State
    String user1 = "userOne";
    List<String> groupsUser1 = new ArrayList<>();
    groupsUser1.add("groupA");
    groupsUser1.add("groupB");
    userToGroup.put(user1, groupsUser1);

    String user2 = "userTwo";
    List<String> groupsUser2 = new ArrayList<>();
    groupsUser2.add("groupB");
    groupsUser2.add("groupC");
    userToGroup.put(user2, groupsUser2);

    ldapGroups.add("groupA");
    ldapGroups.add("groupB");
    ldapGroups.add("groupC");

    // Setup DB State
    dbStateSuperusers.add("groupA");
    dbStateSuperusers.add("groupC");
    dbStateSuperusers.add("groupD");

    String user1DB = "userOne";
    List<String> groupsUser1DB = new ArrayList<>();
    groupsUser1DB.add("groupA");
    groupsUser1DB.add("groupC");
    dbStateUsers.put(user1DB, groupsUser1DB);

    String user2DB = "userThree";
    List<String> groupsUser2DB = new ArrayList<>();
    groupsUser2DB.add("groupD");
    dbStateUsers.put(user2DB, groupsUser2DB);

    dbStateUsers.put("groupA", new ArrayList<>());
    dbStateUsers.put("groupC", new ArrayList<>());
    dbStateUsers.put("groupD", new ArrayList<>());

    params = new LdapUnivSync.Params();
    params.userToGroup = userToGroup;
    params.ldapGroups = ldapGroups;

    task = new DbLdapSync(mockBaseTaskDependencies, mockYsqlQueryExecutor, mockYcqlQueryExecutor);
    task.initialize(params);
  }

  /* ==== API Tests ==== */
  @Test
  public void testQueriesCreateGroups() {
    // ldapGroups: {A,B,C} dbSuperusers: {A,C,D} : Create groups B on DB
    List<String> queriesYsql = task.computeQueriesCreateGroups(dbStateSuperusers, true);
    List<String> queriesYcql = task.computeQueriesCreateGroups(dbStateSuperusers, false);

    assertTrue(
        queriesYsql.get(0).contains("CREATE ROLE \"groupB\" WITH SUPERUSER LOGIN PASSWORD "));
    assertEquals(queriesYsql.size(), 1);

    assertTrue(
        queriesYcql.get(0).contains("CREATE ROLE IF NOT EXISTS \"groupB\" WITH SUPERUSER = true"));
    assertEquals(queriesYcql.size(), 1);
  }

  @Test
  public void testQueriesUsers() {
    // dbState: userOne:{A,C} userThree:{D} A:{} C:{} D:{} and ldapState: userOne:{A,B}
    // userTwo:{B,C}
    // ldapGroups: A, B, C dbStateSuperusers: A, C, D
    // diff: not equal: only on left={groupD=[], userThree=[groupD], groupA=[], groupC=[]}: only on
    // right={userTwo=[groupB, groupC]}: value differences={userOne=([groupA, groupC], [groupA,
    // groupB])}
    List<String> excludeUsers = new ArrayList<>();
    List<String> queriesYsql =
        task.computeQueriesViaDiffUsers(dbStateUsers, dbStateSuperusers, true, excludeUsers, false);
    List<String> queriesYcql =
        task.computeQueriesViaDiffUsers(
            dbStateUsers, dbStateSuperusers, false, excludeUsers, false);

    // queries: create userTwo, grant B to userTwo, grant C to userTwo, revoke C from userone, grant
    // B to userOne,
    // drop userThree
    assertTrue(queriesYsql.get(0).contains("CREATE ROLE \"userTwo\" WITH LOGIN PASSWORD "));
    assertEquals(queriesYsql.get(1), "GRANT \"groupB\" TO \"userTwo\";");
    assertEquals(queriesYsql.get(2), "GRANT \"groupC\" TO \"userTwo\";");
    assertEquals(queriesYsql.get(3), "REVOKE \"groupC\" FROM \"userOne\";");
    assertEquals(queriesYsql.get(4), "GRANT \"groupB\" TO \"userOne\";");
    assertEquals(queriesYsql.get(5), "DROP ROLE IF EXISTS \"userThree\";");

    assertTrue(
        queriesYcql
            .get(0)
            .contains("CREATE ROLE IF NOT EXISTS \"userTwo\" WITH SUPERUSER = false"));
    assertEquals(queriesYcql.get(1), "GRANT \"groupB\" TO \"userTwo\";");
    assertEquals(queriesYcql.get(2), "GRANT \"groupC\" TO \"userTwo\";");
    assertEquals(queriesYcql.get(3), "REVOKE \"groupC\" FROM \"userOne\";");
    assertEquals(queriesYcql.get(4), "GRANT \"groupB\" TO \"userOne\";");
    assertEquals(queriesYcql.get(5), "DROP ROLE IF EXISTS \"userThree\";");

    excludeUsers.add("userThree");
    queriesYsql =
        task.computeQueriesViaDiffUsers(dbStateUsers, dbStateSuperusers, true, excludeUsers, false);
    queriesYcql =
        task.computeQueriesViaDiffUsers(
            dbStateUsers, dbStateSuperusers, false, excludeUsers, false);

    assertFalse(queriesYsql.contains("DROP ROLE IF EXISTS \"userThree\";"));
    assertFalse(queriesYcql.contains("DROP ROLE IF EXISTS \"userThree\";"));

    // drop D
    queriesYsql =
        task.computeQueriesViaDiffUsers(dbStateUsers, dbStateSuperusers, true, excludeUsers, true);
    queriesYcql =
        task.computeQueriesViaDiffUsers(dbStateUsers, dbStateSuperusers, false, excludeUsers, true);

    assertTrue(queriesYsql.contains("DROP ROLE IF EXISTS \"groupD\";"));
    assertTrue(queriesYcql.contains("DROP ROLE IF EXISTS \"groupD\";"));
  }
}
