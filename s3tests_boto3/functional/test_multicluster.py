import boto3
import botocore.session
from botocore.exceptions import ClientError
from botocore.exceptions import ParamValidationError
from nose.tools import eq_ as eq
from nose.plugins.attrib import attr
from nose.plugins.skip import SkipTest
import isodate
import email.utils
import datetime
import threading
import re
import pytz
from collections import OrderedDict
import requests
import json
import base64
import hmac
import hashlib
import xml.etree.ElementTree as ET
import time
import operator
import nose
import os
import string
import random
import socket
import dateutil.parser
import ssl
from collections import namedtuple
from time import sleep

from email.header import decode_header

from .utils import assert_raises
from .utils import generate_random
from .utils import _get_status_and_error_code
from .utils import _get_status

from .policy import Policy, Statement, make_json_policy

from . import (
    get_client,
    get_prefix,
    get_unauthenticated_client,
    get_bad_auth_client,
    get_v2_client,
    get_new_bucket,
    get_new_bucket_name,
    get_new_bucket_resource,
    get_same_bucket_resource,
    get_config_is_secure,
    get_config_host,
    get_config_port,
    get_config_endpoint,
    get_main_aws_access_key,
    get_main_aws_secret_key,
    get_main_display_name,
    get_main_user_id,
    get_main_email,
    get_main_api_name,
    get_alt_aws_access_key,
    get_alt_aws_secret_key,
    get_alt_display_name,
    get_alt_user_id,
    get_alt_email,
    get_alt_client,
    get_tenant_client,
    get_tenant_iam_client,
    get_tenant_user_id,
    get_buckets_list,
    get_objects_list,
    get_main_kms_keyid,
    get_secondary_kms_keyid,
    get_svc_client,
    nuke_prefixed_buckets,
    )


def migrate():
    sleep(1)

def _create_bucket_with_objects(bucket=None, bucket_name=None, keys=[], use_second=None):
    """
    Populate a (new or specified) bucket with objects with
    specified names (and contents identical to their names).
    """
    if bucket_name is None:
        bucket_name = get_new_bucket_name()

    if bucket is None:
        bucket = get_new_bucket_resource(name=bucket_name, use_second=use_second)

    for key in keys:
        obj = bucket.put_object(Body=key, Key=key)

    return bucket_name

def _get_keys(response):
    """
    return lists of strings that are the keys from a client.list_objects() response
    """
    keys = []
    if 'Contents' in response:
        objects_list = response['Contents']
        keys = [obj['Key'] for obj in objects_list]
    return keys
    
def _bucket_is_empty(bucket):
    is_empty = True
    for obj in bucket.objects.all():
        is_empty = False
        break
    return is_empty

# def test_connections():
#     cluster1 = get_client()
#     cluster2 = get_client(use_second=True)

@attr(resource='bucket')
@attr(method='get')
@attr(operation='list')
@attr(assertion='empty buckets return no contents')
def test_bucket_list_empty():
    """
    Tests the connection to both clusters 
    And also that both buckets are currently empty
    (clean test state)
    """
    bucket = get_new_bucket_resource()
    is_empty = _bucket_is_empty(bucket)
    eq(is_empty, True)
    bucket2 = get_new_bucket_resource(use_second=True)
    is_empty = _bucket_is_empty(bucket2)
    eq(is_empty, True)

@attr('multicluster')
@attr(resource='bucket')
@attr(method='get')
@attr(operation='list')
@attr(assertion='distinct buckets have different contents')
def test_bucket_list_distinct():
    """
    Migrates buckets to the second cluster and tests contents
    Small buckets, no ACL checks
    """
    bucket1 = get_new_bucket_resource()
    bucket2 = get_new_bucket_resource()
    obj = bucket1.put_object(Body='str', Key='asdf')
    is_empty = _bucket_is_empty(bucket2)
    eq(is_empty, True)

    migrate()

    bucket1_2 = get_same_bucket_resource(bucket1, use_second=True)
    bucket2_2 = get_same_bucket_resource(bucket2, use_second=True)
    eq(bucket1, bucket1_2)
    is_empty = _bucket_is_empty(bucket2_2)
    eq(is_empty, True)

@attr(resource='bucket')
@attr(method='get')
@attr(operation='list all keys')
@attr(assertion='pagination w/max_keys=2, no marker')
def test_bucket_list_many():
    """
    Tests pagination of object retrieval on both clusters
    Creates a number of buckets and retrieves with pagination set to 2
    """
    bucket_name = _create_bucket_with_objects(keys=['foo', 'bar', 'baz'])

    client1 = get_client()

    response = client1.list_objects(Bucket=bucket_name, MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 2)
    eq(keys, ['bar', 'baz'])
    eq(response['IsTruncated'], True)

    response = client1.list_objects(Bucket=bucket_name, Marker='baz',MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 1)
    eq(response['IsTruncated'], False)
    eq(keys, ['foo'])

    migrate()

    client2 = get_client(use_second=True)
    response = client2.list_objects(Bucket=bucket_name, MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 2)
    eq(keys, ['bar', 'baz'])
    eq(response['IsTruncated'], True)

    response = client2.list_objects(Bucket=bucket_name, Marker='baz',MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 1)
    eq(response['IsTruncated'], False)
    eq(keys, ['foo'])

@attr(resource='bucket')
@attr(method='get')
@attr(operation='get bucket policy status on a new bucket')
@attr(assertion='succeeds')
@attr('policy_status')
def test_get_bucket_policy_status():
    '''
    test default policy status for buckets is non public
    ensure that that status is preserved accross migration
    '''
    bucket_name = get_new_bucket()
    client1 = get_client()
    resp = client1.get_bucket_policy_status(Bucket=bucket_name)
    eq(resp['PolicyStatus']['IsPublic'],False)
    
    migrate()

    client2 = get_client(use_second=True)
    resp = client2.get_bucket_policy_status(Bucket=bucket_name)
    eq(resp['PolicyStatus']['IsPublic'],False)


@attr(resource='bucket')
@attr(method='get')
@attr(operation='Test Bucket Policy')
@attr(assertion='succeeds')
@attr('bucket-policy')
def test_bucket_policy():
    '''
    Set bucket policy explicitly and test it's preserved in the migration
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    key = 'asdf'
    client1.put_object(Bucket=bucket_name, Key=key, Body='asdf')

    resource1 = "arn:aws:s3:::" + bucket_name
    resource2 = "arn:aws:s3:::" + bucket_name + "/*"
    policy_document = json.dumps(
    {
        "Version": "2012-10-17",
        "Statement": [{
        "Effect": "Allow",
        "Principal": {"AWS": "*"},
        "Action": "s3:ListBucket",
        "Resource": [
            "{}".format(resource1),
            "{}".format(resource2)
          ]
        }]
     })

    client1.put_bucket_policy(Bucket=bucket_name, Policy=policy_document)

    alt_client1 = get_alt_client()
    response = alt_client1.list_objects(Bucket=bucket_name)
    eq(len(response['Contents']), 1)

    migrate()

    client2 = get_client(use_second=True)
    response = client2.get_bucket_policy(Bucket=bucket_name)
    eq(response['Policy'], policy_document, "migrated bucket policy document doesn't match")
    
    alt_client2 = get_alt_client(use_second=True)
    response = alt_client2.list_objects(Bucket=bucket_name)
    eq(len(response['Contents']), 1)

@nose.tools.nottest
@attr(resource='object')
@attr(method='put')
@attr(operation='Test put obj with canned-acl not to be public')
@attr(assertion='success')
@attr('tagging')
@attr('bucket-policy')
def test_bucket_policy_put_obj_acl():
    '''
    test canned-acl is not public
    Makes a new obj with canned acl and tries to access it from the public
    should fail. migrating bucket should keep same canned acl
    '''
    bucket_name = get_new_bucket()
    client = get_client()

    # An allow conditional will require atleast the presence of an x-amz-acl
    # attribute a Deny conditional would negate any requests that try to set a
    # public-read/write acl
    conditional = {"StringLike": {
        "s3:x-amz-acl" : "public*"
    }}

    def _make_arn_resource(path="*"):
        return "arn:aws:s3:::{}".format(path)

    p = Policy()
    resource = _make_arn_resource("{}/{}".format(bucket_name, "*"))
    s1 = Statement("s3:PutObject",resource)
    s2 = Statement("s3:PutObject", resource, effect="Deny", condition=conditional)

    policy_document = p.add_statement(s1).add_statement(s2).to_json()
    client.put_bucket_policy(Bucket=bucket_name, Policy=policy_document)

    alt_client1 = get_alt_client()
    key1 = 'private-key'

    # if we want to be really pedantic, we should check that this doesn't raise
    # and mark a failure, however if this does raise nosetests would mark this
    # as an ERROR anyway
    response = alt_client1.put_object(Bucket=bucket_name, Key=key1, Body=key1)
    #response = alt_client.put_object_acl(Bucket=bucket_name, Key=key1, ACL='private')
    eq(response['ResponseMetadata']['HTTPStatusCode'], 200)

    key2 = 'public-key'

    lf = (lambda **kwargs: kwargs['params']['headers'].update({"x-amz-acl": "public-read"}))
    alt_client1.meta.events.register('before-call.s3.PutObject', lf)

    e = assert_raises(ClientError, alt_client1.put_object, Bucket=bucket_name, Key=key2, Body=key2)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)

    migrate()

    # check that the migrated bucket has the same end behaviour

    # TODO: currently is failing to raise an error. Might need to add in the lanmbda function
    alt_client2 = get_alt_client(use_second=True)
    e = assert_raises(ClientError, alt_client2.put_object, Bucket=bucket_name, Key=key2, Body=key2)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)


@attr(resource='bucket')
@attr(method='get')
@attr(operation='Test Bucket Policy and ACL')
@attr(assertion='fails')
@attr('bucket-policy')
def test_bucket_policy_acl():
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    key = 'asdf'
    client1.put_object(Bucket=bucket_name, Key=key, Body='asdf')

    resource1 = "arn:aws:s3:::" + bucket_name
    resource2 = "arn:aws:s3:::" + bucket_name + "/*"
    policy_document =  json.dumps(
    {
        "Version": "2012-10-17",
        "Statement": [{
        "Effect": "Deny",
        "Principal": {"AWS": "*"},
        "Action": "s3:ListBucket",
        "Resource": [
            "{}".format(resource1),
            "{}".format(resource2)
          ]
        }]
     })

    client1.put_bucket_acl(Bucket=bucket_name, ACL='authenticated-read')
    client1.put_bucket_policy(Bucket=bucket_name, Policy=policy_document)

    alt_client1 = get_alt_client()
    e = assert_raises(ClientError, alt_client1.list_objects, Bucket=bucket_name)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')

    migrate()

    alt_client2 = get_alt_client(use_second=True)
    e = assert_raises(ClientError, alt_client2.list_objects, Bucket=bucket_name)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')

    # clean up
    client1.delete_bucket_policy(Bucket=bucket_name)
    client1.put_bucket_acl(Bucket=bucket_name, ACL='public-read')

def add_bucket_user_grant(bucket_name, grant, client=None, use_second=False):
    """
    Adds a grant to the existing grants meant to be passed into
    the AccessControlPolicy argument of put_object_acls for an object
    owned by the main user, not the alt user
    A grant is a dictionary in the form of:
    {u'Grantee': {u'Type': 'type', u'DisplayName': 'name', u'ID': 'id'}, u'Permission': 'PERM'}
    """
    if client is None:
        client = get_client(use_second=use_second)

    main_user_id = get_main_user_id()
    main_display_name = get_main_display_name()

    response = client.get_bucket_acl(Bucket=bucket_name)

    grants = response['Grants']
    grants.append(grant)

    grant = {'Grants': grants, 'Owner': {'DisplayName': main_display_name, 'ID': main_user_id}}

    return grant

@attr(resource='bucket')
@attr(method='ACLs')
@attr(operation='set acl w/invalid userid')
@attr(assertion='fails 400')
def test_bucket_acl_grant_nonexist_user():
    '''
    Test acl with user who is not created
    create bucket, set permissions to allow usserid which doesn't exist
    test that response back fails when trying to access
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)

    bad_user_id = '_foo'

    #response = client.get_bucket_acl(Bucket=bucket_name)
    grant = {'Grantee': {'ID': bad_user_id, 'Type': 'CanonicalUser' }, 'Permission': 'FULL_CONTROL'}

    grant = add_bucket_user_grant(bucket_name, grant)

    e = assert_raises(ClientError, client1.put_bucket_acl, Bucket=bucket_name, AccessControlPolicy=grant)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')

    migrate()

    client2 = get_client(use_second=True)
    e = assert_raises(ClientError, client2.put_bucket_acl, Bucket=bucket_name, AccessControlPolicy=grant)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')

def _bucket_acl_grant_userid(permission):
    """
    create a new bucket, grant the alt user the specified
    permission, read back the acl and verify correct setting
    """
    bucket_name = get_new_bucket()
    client = get_client()

    main_user_id = get_main_user_id()
    main_display_name = get_main_display_name()

    alt_user_id = get_alt_user_id()
    alt_display_name = get_alt_display_name()

    grant = {'Grantee': {'ID': alt_user_id, 'Type': 'CanonicalUser' }, 'Permission': permission}

    grant = add_bucket_user_grant(bucket_name, grant)

    client.put_bucket_acl(Bucket=bucket_name, AccessControlPolicy=grant)

    response = client.get_bucket_acl(Bucket=bucket_name)

    grants = response['Grants']
    check_grants(
        grants,
        [
            dict(
                Permission=permission,
                ID=alt_user_id,
                DisplayName=alt_display_name,
                URI=None,
                EmailAddress=None,
                Type='CanonicalUser',
                ),
            dict(
                Permission='FULL_CONTROL',
                ID=main_user_id,
                DisplayName=main_display_name,
                URI=None,
                EmailAddress=None,
                Type='CanonicalUser',
                ),
            ],
        )

    return bucket_name

'''
The following tests are for testing alt user permissions on specificed bucket
'''

def _check_bucket_acl_grant_can_read(bucket_name, use_second=False):
    """
    verify ability to read the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    response = alt_client.head_bucket(Bucket=bucket_name)

def _check_bucket_acl_grant_cant_read(bucket_name, use_second=False):
    """
    verify inability to read the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    check_access_denied(alt_client.head_bucket, Bucket=bucket_name)

def _check_bucket_acl_grant_can_readacp(bucket_name, use_second=False):
    """
    verify ability to read acls on specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    alt_client.get_bucket_acl(Bucket=bucket_name)

def _check_bucket_acl_grant_cant_readacp(bucket_name, use_second=False):
    """
    verify inability to read acls on specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    check_access_denied(alt_client.get_bucket_acl, Bucket=bucket_name)

def _check_bucket_acl_grant_can_write(bucket_name, use_second=False):
    """
    verify ability to write the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    alt_client.put_object(Bucket=bucket_name, Key='foo-write', Body='bar')

def _check_bucket_acl_grant_cant_write(bucket_name, use_second=False):

    """
    verify inability to write the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    check_access_denied(alt_client.put_object, Bucket=bucket_name, Key='foo-write', Body='bar')

def _check_bucket_acl_grant_can_writeacp(bucket_name, use_second=False):
    """
    verify ability to set acls on the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    alt_client.put_bucket_acl(Bucket=bucket_name, ACL='public-read')

def _check_bucket_acl_grant_cant_writeacp(bucket_name, use_second=False):
    """
    verify inability to set acls on the specified bucket
    """
    alt_client = get_alt_client(use_second=use_second)
    check_access_denied(alt_client.put_bucket_acl,Bucket=bucket_name, ACL='public-read')

@attr(resource='bucket')
@attr(method='ACLs')
@attr(operation='set acl w/userid WRITE')
@attr(assertion='can write data, no other r/w')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${ALTUSER}</ArgumentValue>
def test_bucket_acl_grant_userid_write():
    '''
    Create bucket with write permisions for alt user and test its correct
    migrate the bucket and verify that same settings are upheld on second cluster
    '''
    bucket_name = _bucket_acl_grant_userid('WRITE')

    # alt user can't read
    _check_bucket_acl_grant_cant_read(bucket_name)
    # can't read acl
    _check_bucket_acl_grant_cant_readacp(bucket_name)
    # can write
    _check_bucket_acl_grant_can_write(bucket_name)
    # can't write acl
    _check_bucket_acl_grant_cant_writeacp(bucket_name)

    migrate()

    # alt user can't read
    _check_bucket_acl_grant_cant_read(bucket_name, use_second=True)
    # can't read acl
    _check_bucket_acl_grant_cant_readacp(bucket_name, use_second=True)
    # can write
    _check_bucket_acl_grant_can_write(bucket_name, use_second=True)
    # can't write acl
    _check_bucket_acl_grant_cant_writeacp(bucket_name, use_second=True)

@attr(resource='bucket')
@attr(method='ACLs')
@attr(operation='set acl w/userid READ')
@attr(assertion='can read data, no other r/w')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${ALTUSER}</ArgumentValue>
def test_bucket_acl_grant_userid_read():
    '''
    Test Read ACL permissions for bucket
    create bucket with read permisions under main user
    migrate and test permissions preserved on second cluster
    '''
    bucket_name = _bucket_acl_grant_userid('READ')

    # alt user can read
    _check_bucket_acl_grant_can_read(bucket_name)
    # can't read acl
    _check_bucket_acl_grant_cant_readacp(bucket_name)
    # can't write
    _check_bucket_acl_grant_cant_write(bucket_name)
    # can't write acl
    _check_bucket_acl_grant_cant_writeacp(bucket_name)

    migrate()

    # alt user can read
    _check_bucket_acl_grant_can_read(bucket_name, use_second=True)
    # can't read acl
    _check_bucket_acl_grant_cant_readacp(bucket_name, use_second=True)
    # can't write
    _check_bucket_acl_grant_cant_write(bucket_name, use_second=True)
    # can't write acl
    _check_bucket_acl_grant_cant_writeacp(bucket_name, use_second=True)

@attr(resource='bucket')
@attr(method='ACLs')
@attr(operation='set acl w/userid FULL_CONTROL')
@attr(assertion='can read/write data/acls')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${USER}</ArgumentValue>
def test_bucket_acl_grant_userid_fullcontrol():
    '''
    test full control permissions for bucket
    Create bucket with full control for main and alt user
    test that bucket is accessible in the same way after migration
    '''
    bucket_name = _bucket_acl_grant_userid('FULL_CONTROL')

    # alt user can read
    _check_bucket_acl_grant_can_read(bucket_name)
    # can read acl
    _check_bucket_acl_grant_can_readacp(bucket_name)
    # can write
    _check_bucket_acl_grant_can_write(bucket_name)
    # can write acl
    _check_bucket_acl_grant_can_writeacp(bucket_name)

    client1 = get_client()

    bucket_acl_response = client1.get_bucket_acl(Bucket=bucket_name)
    owner_id = bucket_acl_response['Owner']['ID']
    owner_display_name = bucket_acl_response['Owner']['DisplayName']

    main_display_name = get_main_display_name()
    main_user_id = get_main_user_id()

    eq(owner_id, main_user_id)
    eq(owner_display_name, main_display_name)

    migrate()

    # alt user can read
    _check_bucket_acl_grant_can_read(bucket_name, use_second=True)
    # can read acl
    _check_bucket_acl_grant_can_readacp(bucket_name, use_second=True)
    # can write
    _check_bucket_acl_grant_can_write(bucket_name, use_second=True)
    # can write acl
    _check_bucket_acl_grant_can_writeacp(bucket_name, use_second=True)

    client2 = get_client(use_second=True)

    bucket_acl_response = client2.get_bucket_acl(Bucket=bucket_name)
    owner_id = bucket_acl_response['Owner']['ID']
    owner_display_name = bucket_acl_response['Owner']['DisplayName']

    main_display_name = get_main_display_name()
    main_user_id = get_main_user_id()

    eq(owner_id, main_user_id)
    eq(owner_display_name, main_display_name)


def _create_key_with_random_content(keyname, size=7*1024*1024, bucket_name=None, client=None):
    # populate object with random data of specified size
    if bucket_name is None:
        bucket_name = get_new_bucket()

    if client == None:
        client = get_client()

    data_str = str(next(generate_random(size, size)))
    data = bytes(data_str, 'utf-8')
    client.put_object(Bucket=bucket_name, Key=keyname, Body=data)

    return bucket_name

@attr(resource='object')
@attr(method='get')
@attr(operation='Test GetObjTagging public read')
@attr(assertion='success')
@attr('tagging')
@attr('bucket-policy')
def test_get_tags_acl_public():
    '''
    create acl tags for object and test existence
    grab tags from alt client and match with tag set
    '''
    key = 'testputtagsacl'
    client1 = get_client()
    bucket_name = _create_key_with_random_content(key, client=client1)

    resource = "arn:aws:s3:::{}/{}".format(bucket_name, key)

    policy_document = make_json_policy("s3:GetObjectTagging",
                                       resource)

    client1.put_bucket_policy(Bucket=bucket_name, Policy=policy_document)

    input_tagset = {'TagSet': []}
    for i in range(10):
        input_tagset['TagSet'].append({'Key': str(i), 'Value': str(i)})

    response = client1.put_object_tagging(Bucket=bucket_name, Key=key, Tagging=input_tagset)
    eq(response['ResponseMetadata']['HTTPStatusCode'], 200)

    alt_client1 = get_alt_client()

    response = alt_client1.get_object_tagging(Bucket=bucket_name, Key=key)
    eq(response['TagSet'], input_tagset['TagSet'])

    migrate()

    client2 = get_client(use_second=True)
    response = client2.get_object_tagging(Bucket=bucket_name, Key=key)
    eq(response['ResponseMetadata']['HTTPStatusCode'], 200)

    alt_client2 = get_alt_client(use_second=True)

    response = alt_client2.get_object_tagging(Bucket=bucket_name, Key=key)
    eq(response['TagSet'], input_tagset['TagSet'])

def _setup_bucket_object_acl(bucket_acl, object_acl):
    """
    add a foo key, and specified key and bucket acls to
    a (new or existing) bucket. Uses main client
    """
    bucket_name = get_new_bucket_name()
    client = get_client()
    client.create_bucket(ACL=bucket_acl, Bucket=bucket_name)
    client.put_object(ACL=object_acl, Bucket=bucket_name, Key='foo')

    return bucket_name

@attr(resource='object.acl')
@attr(method='get')
@attr(operation='unauthenticated on private object')
@attr(assertion='fails 403')
@nose.tools.nottest
def test_object_raw_get_object_acl():
    bucket_name = _setup_bucket_object_acl('public-read', 'private')

    unauthenticated_client1 = get_unauthenticated_client()
    e = assert_raises(ClientError, unauthenticated_client1.get_object, Bucket=bucket_name, Key='foo')
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')

    migrate()

    unauthenticated_client2 = get_unauthenticated_client(use_second=true)
    e = assert_raises(ClientError, unauthenticated_client2.get_object, Bucket=bucket_name, Key='foo')
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 403)
    eq(error_code, 'AccessDenied')