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

class FakeFile(object):
    """
    file that simulates seek, tell, and current character
    """
    def __init__(self, char='A', interrupt=None):
        self.offset = 0
        self.char = bytes(char, 'utf-8')
        self.interrupt = interrupt

    def seek(self, offset, whence=os.SEEK_SET):
        if whence == os.SEEK_SET:
            self.offset = offset
        elif whence == os.SEEK_END:
            self.offset = self.size + offset;
        elif whence == os.SEEK_CUR:
            self.offset += offset

    def tell(self):
        return self.offset

class FakeWriteFile(FakeFile):
    """
    file that simulates interruptable reads of constant data
    """
    def __init__(self, size, char='A', interrupt=None):
        FakeFile.__init__(self, char, interrupt)
        self.size = size

    def read(self, size=-1):
        if size < 0:
            size = self.size - self.offset
        count = min(size, self.size - self.offset)
        self.offset += count

        # Sneaky! do stuff before we return (the last time)
        if self.interrupt != None and self.offset == self.size and count > 0:
            self.interrupt()

        return self.char*count

def _make_random_string(size):
    return ''.join(random.choice(string.ascii_letters) for _ in range(size))

def _get_body(response):
    body = response['Body']
    got = body.read()
    if type(got) is bytes:
        got = got.decode()
    return got

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

def _setup_bucket_object_acl(bucket_acl, object_acl, client=None):
    """
    add a foo key, and specified key and bucket acls to
    a (new or existing) bucket. Uses main client
    """
    if client is None:
        client = get_client()
    bucket_name = get_new_bucket_name(client=client)
    client.create_bucket(ACL=bucket_acl, Bucket=bucket_name)
    client.put_object(ACL=object_acl, Bucket=bucket_name, Key='foo')

    return bucket_name

@attr(resource='object.acl')
@attr(method='get')
@attr(operation='unauthenticated on private object')
@attr(assertion='fails 403')
@nose.tools.nottest # fails test right now
def test_object_raw_get_object_acl():
    '''
    create raw object with private access and public-read ACL, test perms
    Try to grab object from unauthed client, pre and post migration
    Test errors are raised 
    '''
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

def check_grants(got, want):
    """
    Check that grants list in got matches the dictionaries in want,
    in any order.
    """
    eq(len(got), len(want))
    for g, w in zip(got, want):
        w = dict(w)
        g = dict(g)
        eq(g.pop('Permission', None), w['Permission'])
        eq(g['Grantee'].pop('DisplayName', None), w['DisplayName'])
        eq(g['Grantee'].pop('ID', None), w['ID'])
        eq(g['Grantee'].pop('Type', None), w['Type'])
        eq(g['Grantee'].pop('URI', None), w['URI'])
        eq(g['Grantee'].pop('EmailAddress', None), w['EmailAddress'])
        eq(g, {'Grantee': {}})

def _check_object_acl(permission):
    """
    Sets the permission on an object then checks to see
    if it was set
    """
    permission = 'FULL_CONTROL'
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)

    client1.put_object(Bucket=bucket_name, Key='foo', Body='bar')

    response = client1.get_object_acl(Bucket=bucket_name, Key='foo')

    policy = {}
    policy['Owner'] = response['Owner']
    policy['Grants'] = response['Grants']
    policy['Grants'][0]['Permission'] = permission

    client1.put_object_acl(Bucket=bucket_name, Key='foo', AccessControlPolicy=policy)

    response = client1.get_object_acl(Bucket=bucket_name, Key='foo')
    grants = response['Grants']

    main_user_id = get_main_user_id()
    main_display_name = get_main_display_name()

    check_grants(
        grants,
        [
            dict(
                Permission=permission,
                ID=main_user_id,
                DisplayName=main_display_name,
                URI=None,
                EmailAddress=None,
                Type='CanonicalUser',
                ),
            ],
        )

    migrate()

    client2 = get_client(use_second=True)

    response = client2.get_object_acl(Bucket=bucket_name, Key='foo')
    grants = response['Grants']

    check_grants(
        grants,
        [
            dict(
                Permission=permission,
                ID=main_user_id,
                DisplayName=main_display_name,
                URI=None,
                EmailAddress=None,
                Type='CanonicalUser',
                ),
            ],
        )


@attr(resource='object')
@attr(method='ACLs')
@attr(operation='set acl FULL_CONTROL')
@attr(assertion='reads back correctly')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${USER}</ArgumentValue>
def test_object_acl_full_control():
    '''
    Test full control permissions and see that it works
    '''

    _check_object_acl('FULL_CONTROL')

@attr(resource='object')
@attr(method='ACLs')
@attr(operation='set acl WRITE')
@attr(assertion='reads back correctly')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${USER}</ArgumentValue>
def test_object_acl_write():
    '''
    test obj write permissions and check it works
    '''
    _check_object_acl('WRITE')

@attr(resource='object')
@attr(method='ACLs')
@attr(operation='set acl READ')
@attr(assertion='reads back correctly')
@attr('fails_on_aws') #  <Error><Code>InvalidArgument</Code><Message>Invalid id</Message><ArgumentName>CanonicalUser/ID</ArgumentName><ArgumentValue>${USER}</ArgumentValue>
def test_object_acl_read():
    '''
    test obj read permissions for alt client and check it works
    '''
    _check_object_acl('READ')

@attr(resource='object')
@attr(method='get')
@attr(operation='get w/ If-Modified-Since: after')
@attr(assertion='fails 304')
def test_get_object_ifmodifiedsince_failed():
    '''
    test that a message does not show as modified after migration
    create object, check modify does not show true
    migrate and check that modify timestamp has not changed
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    client1.put_object(Bucket=bucket_name, Key='foo', Body='bar')
    response = client1.get_object(Bucket=bucket_name, Key='foo')
    last_modified = str(response['LastModified'])

    last_modified = last_modified.split('+')[0]
    mtime = datetime.datetime.strptime(last_modified, '%Y-%m-%d %H:%M:%S')

    after = mtime + datetime.timedelta(seconds=1)
    after_str = time.strftime("%a, %d %b %Y %H:%M:%S GMT", after.timetuple())

    time.sleep(1)

    e = assert_raises(ClientError, client1.get_object, Bucket=bucket_name, Key='foo', IfModifiedSince=after_str)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 304)
    eq(e.response['Error']['Message'], 'Not Modified')

    migrate()

    client2 = get_client(use_second=True)
    e = assert_raises(ClientError, client2.get_object, Bucket=bucket_name, Key='foo', IfModifiedSince=after_str)
    status, error_code = _get_status_and_error_code(e.response)
    eq(status, 304)
    eq(e.response['Error']['Message'], 'Not Modified')

@attr(resource='object')
@attr(method='put')
@attr(operation='migrate zero sized object')
@attr(assertion='works')
def test_object_copy_zero_size():
    '''
    test an object of 0 size is migrated correctly
    create a file in og bucket with size of 0
    migrate over and check bucket exists and size is 0
    '''
    key = 'foo123bar'
    bucket_name = _create_bucket_with_objects(keys=[key])
    fp_a = FakeWriteFile(0, '')
    client1 = get_client()
    client1.put_object(Bucket=bucket_name, Key=key, Body=fp_a)

    migrate(bucket_name)

    client2 = get_client(use_second=True)
    response = client2.get_object(Bucket=bucket_name, Key=key)
    eq(response['ContentLength'], 0)

@attr(resource='object')
@attr(method='put')
@attr(operation='copy object to itself')
@attr(assertion='fails')
def test_object_migrate():
    '''
    test obj migration has same data
    create obj, populate with sample data
    migrate and assert data is preserved
    '''
    bucket_name = get_new_bucket()
    client1 = get_client()
    obj = 'foo123bar'
    client1.put_object(Bucket=bucket_name, Key=obj, Body='foo')

    migrate(bucket_name)

    client2 = get_client(use_second=True)
    response = client2.get_object(Bucket=bucket_name, Key=obj)
    body = _get_body(response)
    eq(body, 'foo')

@attr(resource='object')
@attr(method='put')
@attr(operation='copy object and retain metadata')
def test_object_copy_retaining_metadata():
    '''
    create metadata on objects, and test to see if it's preserved on migration
    '''

    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    content_type = 'audio/ogg'

    obj = 'foo123bar'

    metadata = {'key1': 'value1', 'key2': 'value2'}
    client1.put_object(Bucket=bucket_name, Key=obj, Metadata=metadata, ContentType=content_type, Body=bytearray(1024 * 1024))

    response = client1.get_object(Bucket=bucket_name, Key=obj)
    eq(content_type, response['ContentType'])
    eq(metadata, response['Metadata'])
    body = _get_body(response)
    eq(size, response['ContentLength'])

    migrate()
    
    client2 = get_client(use_second=True)
    response = client2.get_object(Bucket=bucket_name, Key=obj)
    eq(content_type, response['ContentType'])
    eq(metadata, response['Metadata'])
    body = _get_body(response)
    eq(size, response['ContentLength'])

@attr(resource='object')
@attr(method='put')
@attr(operation='lots of object and retain data')
def test_multiple_objects():
    '''
    create 100 objects in a single bucket and test they migrate
    assert that the contents are the same after migration
    '''
    num_objs = 100

    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    keys = map(str, list(range(num_objs)))
    _create_bucket_with_objects(bucket_name=bucket_name, keys=list(keys))

    def check_objs(client, key):
        response = client.get_object(Bucket=bucket_name, Key=key)
        body = _get_body(response)
        eq(key, body)

    (check_objs(client1, key) for key in keys)

    migrate()

    client2 = get_client(use_second=True)
    (check_objs(client2, key) for key in keys)

@attr(resource='object')
@attr(method='put')
@attr(operation='migrate objects with special chars in the name')
def test_objects_special_chars():
    '''
    create objects with special chars in name and test they migrate
    assert that the contents are the same after migration
    '''

    special_chars = list('!@#$%^(){}_')

    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    keys = ['random' + char + 'name' for char in special_chars]
    _create_bucket_with_objects(bucket_name=bucket_name, keys=list(keys))

    def check_objs(client, key):
        response = client.get_object(Bucket=bucket_name, Key=key)
        body = _get_body(response)
        eq(key, body)

    (check_objs(client1, key) for key in keys)

    migrate()

    client2 = get_client(use_second=True)
    (check_objs(client2, key) for key in keys)

@attr(resource='object')
@attr(method='put')
@attr(operation='copy object to/from versioned bucket')
@attr(assertion='works')
@attr('versioning')
@nose.tools.nottest # this test might not actually be fully needed 
def test_object_copy_versioned_bucket():
    '''
    Test versioning system works for migrated bucket
    migrate bucket, ensure that versioning works for copied bucket
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    check_configure_versioning_retry(bucket_name, "Enabled", "Enabled")
    size = 1*5
    data = bytearray(size)
    data_str = data.decode()
    key1 = 'foo123bar'
    client1.put_object(Bucket=bucket_name, Key=key1, Body=data)

    response = client1.get_object(Bucket=bucket_name, Key=key1)
    version_id = response['VersionId']

    # copy object in the same bucket
    copy_source = {'Bucket': bucket_name, 'Key': key1, 'VersionId': version_id}
    key2 = 'bar321foo'
    client1.copy_object(Bucket=bucket_name, CopySource=copy_source, Key=key2)
    response = client1.get_object(Bucket=bucket_name, Key=key2)
    body = _get_body(response)
    eq(data_str, body)
    eq(size, response['ContentLength'])

    migrate()

    client2 = get_client(use_second=True)

    # second copy
    version_id2 = response['VersionId']
    copy_source = {'Bucket': bucket_name, 'Key': key2, 'VersionId': version_id2}
    key3 = 'bar321foo2'
    client2.copy_object(Bucket=bucket_name, CopySource=copy_source, Key=key3)
    response = client2.get_object(Bucket=bucket_name, Key=key3)
    body = _get_body(response)
    eq(data_str, body)
    eq(size, response['ContentLength'])

    # copy to another versioned bucket
    bucket_name2 = get_new_bucket()
    check_configure_versioning_retry(bucket_name2, "Enabled", "Enabled")
    copy_source = {'Bucket': bucket_name, 'Key': key1, 'VersionId': version_id}
    key4 = 'bar321foo3'
    client2.copy_object(Bucket=bucket_name2, CopySource=copy_source, Key=key4)
    response = client2.get_object(Bucket=bucket_name2, Key=key4)
    body = _get_body(response)
    eq(data_str, body)
    eq(size, response['ContentLength'])

    # copy to another non versioned bucket
    bucket_name3 = get_new_bucket()
    copy_source = {'Bucket': bucket_name, 'Key': key1, 'VersionId': version_id}
    key5 = 'bar321foo4'
    client2.copy_object(Bucket=bucket_name3, CopySource=copy_source, Key=key5)
    response = client2.get_object(Bucket=bucket_name3, Key=key5)
    body = _get_body(response)
    eq(data_str, body)
    eq(size, response['ContentLength'])

    # copy from a non versioned bucket
    copy_source = {'Bucket': bucket_name3, 'Key': key5}
    key6 = 'foo123bar2'
    client2.copy_object(Bucket=bucket_name, CopySource=copy_source, Key=key6)
    response = client2.get_object(Bucket=bucket_name, Key=key6)
    body = _get_body(response)
    eq(data_str, body)
    eq(size, response['ContentLength'])

@attr(resource='object')
@attr(method='put')
@attr(operation='check multipart uploads with single small part')
@attr('multipart')
def test_multipart_upload_small():
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)

    key1 = "mymultipart"
    objlen = 1
    (upload_id, data, parts) = _multipart_upload(bucket_name=bucket_name, key=key1, size=objlen)
    response = client1.complete_multipart_upload(Bucket=bucket_name, Key=key1, UploadId=upload_id, MultipartUpload={'Parts': parts})
    response = client1.get_object(Bucket=bucket_name, Key=key1)
    eq(response['ContentLength'], objlen)

    migrate()
    
    client2 = get_client(use_second=True)

    response = client1.get_object(Bucket=bucket_name, Key=key1)
    eq(response['ContentLength'], objlen)

def generate_random(size, part_size=5*1024*1024):
    """
    Generate the specified number random data.
    (actually each MB is a repetition of the first KB)
    """
    chunk = 1024
    allowed = string.ascii_letters
    for x in range(0, size, part_size):
        strpart = ''.join([allowed[random.randint(0, len(allowed) - 1)] for _ in range(chunk)])
        s = ''
        left = size - x
        this_part_size = min(left, part_size)
        for y in range(this_part_size // chunk):
            s = s + strpart
        if this_part_size > len(s):
            s = s + strpart[0:this_part_size - len(s)]
        yield s
        if (x == size):
            return

def _multipart_upload(bucket_name, key, size, part_size=5*1024*1024, client=None, content_type=None, metadata=None, resend_parts=[], start=0):
    """
    generate a multi-part upload for a random file of specifed size,
    if requested, generate a list of the parts
    return the upload descriptor
    """
    if client == None:
        client = get_client()


    if content_type == None and metadata == None:
        response = client.create_multipart_upload(Bucket=bucket_name, Key=key)
    else:
        response = client.create_multipart_upload(Bucket=bucket_name, Key=key, Metadata=metadata, ContentType=content_type)

    upload_id = response['UploadId']
    s = ''
    parts = []
    for i, part in enumerate(generate_random(size, part_size), start):
        # part_num is necessary because PartNumber for upload_part
        part_num = i+1
        s += part
        response = client.upload_part(UploadId=upload_id, Bucket=bucket_name, Key=key, PartNumber=part_num, Body=part)
        parts.append({'ETag': response['ETag'].strip('"'), 'PartNumber': part_num})
        if i in resend_parts:
            client.upload_part(UploadId=upload_id, Bucket=bucket_name, Key=key, PartNumber=part_num, Body=part)
    return (upload_id, s, parts)

def _check_content_using_range(key, bucket_name, data, step, client):
    response = client.get_object(Bucket=bucket_name, Key=key)
    size = response['ContentLength']

    for ofs in range(0, size, step):
        toread = size - ofs
        if toread > step:
            toread = step
        end = ofs + toread - 1
        r = 'bytes={s}-{e}'.format(s=ofs, e=end)
        response = client.get_object(Bucket=bucket_name, Key=key, Range=r)
        eq(response['ContentLength'], toread)
        body = _get_body(response)
        eq(body, data[ofs:end+1])

@attr(resource='object')
@attr(method='put')
@attr(operation='interupt middle of multipart upload with migration')
@attr('multipart')
@nose.tools.nottest
# tests currently broken, will need to revisit the code
def test_multipart_upload_migrate_interupt():
    '''
    Test multipart upload interupted in the middle by a migration 
    If continue uploading after migration, ensure it is correctly uploaded
    '''

    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    key="mymultipart"
    content_type='text/bla'
    objlen = 15 * 1024 * 1024
    metadata = {'foo': 'bar'}
    (upload_id1, data1, parts1) = _multipart_upload(bucket_name=bucket_name, key=key, size=objlen, content_type=content_type, metadata=metadata)

    # simulate stopped in the middle of uploading parts
    migrate()

    client2 = get_client(use_second=True)
    (upload_id2, data2, parts2) = _multipart_upload(bucket_name=bucket_name, key=key, size=objlen, content_type=content_type, metadata=metadata, start=len(parts1))
    client2.complete_multipart_upload(Bucket=bucket_name, Key=key, UploadId=upload_id2, MultipartUpload={'Parts': parts1 + parts2})

    response = client2.head_bucket(Bucket=bucket_name)
    rgw_bytes_used = int(response['ResponseMetadata']['HTTPHeaders'].get('x-rgw-bytes-used', objlen*2))
    eq(rgw_bytes_used, objlen*2)

    rgw_object_count = int(response['ResponseMetadata']['HTTPHeaders'].get('x-rgw-object-count', 1))
    eq(rgw_object_count, 1)

    response = client2.get_object(Bucket=bucket_name, Key=key)
    eq(response['ContentType'], content_type)
    eq(response['Metadata'], metadata)
    body = _get_body(response)
    total_data = data1 + data2
    eq(len(body), response['ContentLength'])
    eq(body, total_data)

    _check_content_using_range(key, bucket_name, total_data, 1000000, client=client2)
    _check_content_using_range(key, bucket_name, total_data, 10000000, client=client2)


@attr(resource='object')
@attr(method='put')
@attr(operation='complete multiple multi-part upload with different sizes')
@attr(resource='object')
@attr(method='put')
@attr(operation='complete multi-part upload')
@attr(assertion='successful')
@attr('multipart')
@nose.tools.nottest
# tests currently broken, will need to revisit the code
def test_multipart_upload_resend_part():
    '''
    test reupload of mulipart pieces after migration works
    multipart upload, migrate before complete
    reupload several pieces, then complete and ensure data is still good
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    key="mymultipart"
    objlen = 30 * 1024 * 1024

    content_type = 'text/bla'
    metadata = {'foo': 'bar'}
    client1 = get_client()
    (upload_id, data, parts) = _multipart_upload(bucket_name=bucket_name, client=client1, key=key, size=objlen/2, content_type=content_type, metadata=metadata)

    migrate()

    # split data into parts again and reupload every other
    def reupload(client, data):
        for i, part in enumerate(data):
            part_num = i+1
            if i % 2 == 0:
                continue
            client.upload_part(UploadId=upload_id, Bucket=bucket_name, Key=key, PartNumber=part_num, Body=part)

    client2 = get_client(use_second=True)
    # uploaded data is a complete string, split back into parts
    chunks = [data[i:i+n] for i in range(0, len(str), len(parts))]
    reupload(client2, chunks)
    
    client2.complete_multipart_upload(Bucket=bucket_name, Key=key, UploadId=upload_id, MultipartUpload={'Parts': parts})

    response = client2.get_object(Bucket=bucket_name, Key=key)
    eq(response['ContentType'], content_type)
    eq(response['Metadata'], metadata)
    body = _get_body(response)
    eq(len(body), response['ContentLength'])
    eq(body, data)

    _check_content_using_range(key, bucket_name, data, 1000000, client=client2)
    _check_content_using_range(key, bucket_name, data, 10000000, client=client2)

@attr(resource='bucket')
@attr(method='put')
@attr(operation='test lifecycle multipart expiration')
@attr('lifecycle')
@attr('lifecycle_expiration')
@attr('fails_on_aws')
@attr('multipart')
@nose.tools.nottest
# currently failing tests on expired upload assertion. Assertion turns up both uploads are expired
def test_lifecycle_multipart_expiration():
    '''
    test that assigning lifecycle policy expires correctly
    create 2 mulitparts and assign lifecycle policy to one of them
    migrate over, then test expiration happened correctly
    '''
    client1 = get_client()
    bucket_name = get_new_bucket()

    key_names = ['test1/a', 'test2/']

    for key in key_names:
        (upload_id, data, parts) = _multipart_upload(bucket_name=bucket_name, client=client1, key=key, size=10)
        # client1.complete_multipart_upload(Bucket=bucket_name, Key=key, UploadId=upload_id, MultipartUpload={'Parts': parts})

    response = client1.list_multipart_uploads(Bucket=bucket_name)
    init_uploads = response['Uploads']

    rules = [
        {'ID': 'rule1', 'Prefix': 'test1/', 'Status': 'Enabled',
         'AbortIncompleteMultipartUpload': {'DaysAfterInitiation': 2}},
    ]
    lifecycle = {'Rules': rules}
    response = client1.put_bucket_lifecycle_configuration(Bucket=bucket_name, LifecycleConfiguration=lifecycle)
    sleep(50)
    migrate()

    client2 = get_client(use_second=True)

    response = client2.list_multipart_uploads(Bucket=bucket_name)
    expired_uploads = response['Uploads']
    eq(len(init_uploads), 2)
    eq(len(expired_uploads), 1)

@attr(resource='bucket')
@attr(method='get')
@attr(operation='get lifecycle config')
@attr('lifecycle')
def test_lifecycle_get():
    '''
    test lifecycles rules set correctly
    set rules, migrate, assert rules carried over
    '''
    client1 = get_client()
    bucket_name = get_new_bucket(client=client1)
    rules=[{'ID': 'test1/', 'Expiration': {'Days': 31}, 'Prefix': 'test1/', 'Status':'Enabled'},
           {'ID': 'test2/', 'Expiration': {'Days': 120}, 'Prefix': 'test2/', 'Status':'Enabled'}]
    lifecycle = {'Rules': rules}
    client1.put_bucket_lifecycle_configuration(Bucket=bucket_name, LifecycleConfiguration=lifecycle)
    response = client1.get_bucket_lifecycle_configuration(Bucket=bucket_name)
    eq(response['Rules'], rules)

    migrate()

    client2 = get_client(use_second=True)
    response = client2.get_bucket_lifecycle_configuration(Bucket=bucket_name)
    eq(response['Rules'], rules)