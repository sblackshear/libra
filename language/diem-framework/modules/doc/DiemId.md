
<a name="0x1_DiemId"></a>

# Module `0x1::DiemId`

Module managing Diem ID.


-  [Resource `DiemIdDomains`](#0x1_DiemId_DiemIdDomains)
-  [Struct `DiemIdDomain`](#0x1_DiemId_DiemIdDomain)
-  [Resource `DiemIdDomainManager`](#0x1_DiemId_DiemIdDomainManager)
-  [Struct `DiemIdDomainEvent`](#0x1_DiemId_DiemIdDomainEvent)
-  [Constants](#@Constants_0)
-  [Function `create_diem_id_domain`](#0x1_DiemId_create_diem_id_domain)
-  [Function `publish_diem_id_domains`](#0x1_DiemId_publish_diem_id_domains)
-  [Function `has_diem_id_domains`](#0x1_DiemId_has_diem_id_domains)
-  [Function `publish_diem_id_domain_manager`](#0x1_DiemId_publish_diem_id_domain_manager)
-  [Function `update_diem_id_domain`](#0x1_DiemId_update_diem_id_domain)
-  [Function `has_diem_id_domain`](#0x1_DiemId_has_diem_id_domain)
-  [Function `tc_domain_manager_exists`](#0x1_DiemId_tc_domain_manager_exists)


<pre><code><b>use</b> <a href="CoreAddresses.md#0x1_CoreAddresses">0x1::CoreAddresses</a>;
<b>use</b> <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors">0x1::Errors</a>;
<b>use</b> <a href="../../../../../../move-stdlib/docs/Event.md#0x1_Event">0x1::Event</a>;
<b>use</b> <a href="Roles.md#0x1_Roles">0x1::Roles</a>;
<b>use</b> <a href="../../../../../../move-stdlib/docs/Signer.md#0x1_Signer">0x1::Signer</a>;
<b>use</b> <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector">0x1::Vector</a>;
</code></pre>



<a name="0x1_DiemId_DiemIdDomains"></a>

## Resource `DiemIdDomains`

This resource holds an entity's domain names needed to send and receive payments using diem IDs.


<pre><code><b>struct</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a> has key
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>domains: vector&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemId::DiemIdDomain</a>&gt;</code>
</dt>
<dd>
 The list of domain names owned by this parent vasp account
</dd>
</dl>


</details>

<a name="0x1_DiemId_DiemIdDomain"></a>

## Struct `DiemIdDomain`

Struct to store the limit on-chain


<pre><code><b>struct</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemIdDomain</a> has <b>copy</b>, drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>domain: vector&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a name="0x1_DiemId_DiemIdDomainManager"></a>

## Resource `DiemIdDomainManager`



<pre><code><b>struct</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a> has key
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>diem_id_domain_events: <a href="../../../../../../move-stdlib/docs/Event.md#0x1_Event_EventHandle">Event::EventHandle</a>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomainEvent">DiemId::DiemIdDomainEvent</a>&gt;</code>
</dt>
<dd>
 Event handle for <code>domains</code> added or removed events. Emitted every time a domain is added
 or removed to <code>domains</code>
</dd>
</dl>


</details>

<a name="0x1_DiemId_DiemIdDomainEvent"></a>

## Struct `DiemIdDomainEvent`



<pre><code><b>struct</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomainEvent">DiemIdDomainEvent</a> has drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>removed: bool</code>
</dt>
<dd>
 Whether a domain was added or removed
</dd>
<dt>
<code>domain: <a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemId::DiemIdDomain</a></code>
</dt>
<dd>
 Diem ID Domain string of the account
</dd>
<dt>
<code>address: address</code>
</dt>
<dd>
 On-chain account address
</dd>
</dl>


</details>

<a name="@Constants_0"></a>

## Constants


<a name="0x1_DiemId_DOMAIN_LENGTH"></a>



<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_DOMAIN_LENGTH">DOMAIN_LENGTH</a>: u64 = 63;
</code></pre>



<a name="0x1_DiemId_EDIEMIDDOMAIN"></a>

DiemIdDomains resource is not or already published.


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAIN">EDIEMIDDOMAIN</a>: u64 = 0;
</code></pre>



<a name="0x1_DiemId_EDIEMIDDOMAINMANAGER"></a>

DiemIdDomainManager resource is not or already published.


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAINMANAGER">EDIEMIDDOMAINMANAGER</a>: u64 = 1;
</code></pre>



<a name="0x1_DiemId_EDIEMIDDOMAINSNOTPUBLISHED"></a>

DiemIdDomains resource was not published for a VASP account


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAINSNOTPUBLISHED">EDIEMIDDOMAINSNOTPUBLISHED</a>: u64 = 4;
</code></pre>



<a name="0x1_DiemId_EDOMAINALREADYEXISTS"></a>

DiemID domain already exists


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EDOMAINALREADYEXISTS">EDOMAINALREADYEXISTS</a>: u64 = 3;
</code></pre>



<a name="0x1_DiemId_EDOMAINNOTFOUND"></a>

DiemID domain was not found


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EDOMAINNOTFOUND">EDOMAINNOTFOUND</a>: u64 = 2;
</code></pre>



<a name="0x1_DiemId_EINVALIDDIEMIDDOMAIN"></a>

Invalid domain for DiemIdDomain


<pre><code><b>const</b> <a href="DiemId.md#0x1_DiemId_EINVALIDDIEMIDDOMAIN">EINVALIDDIEMIDDOMAIN</a>: u64 = 5;
</code></pre>



<a name="0x1_DiemId_create_diem_id_domain"></a>

## Function `create_diem_id_domain`



<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_create_diem_id_domain">create_diem_id_domain</a>(domain: vector&lt;u8&gt;): <a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemId::DiemIdDomain</a>
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_create_diem_id_domain">create_diem_id_domain</a>(domain: vector&lt;u8&gt;): <a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemIdDomain</a> {
    <b>assert</b>(<a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_length">Vector::length</a>(&domain) &lt;= <a href="DiemId.md#0x1_DiemId_DOMAIN_LENGTH">DOMAIN_LENGTH</a>, <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_invalid_argument">Errors::invalid_argument</a>(<a href="DiemId.md#0x1_DiemId_EINVALIDDIEMIDDOMAIN">EINVALIDDIEMIDDOMAIN</a>));
    <a href="DiemId.md#0x1_DiemId_DiemIdDomain">DiemIdDomain</a> {domain}
}
</code></pre>



</details>

<a name="0x1_DiemId_publish_diem_id_domains"></a>

## Function `publish_diem_id_domains`

Publish a <code><a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a></code> resource under <code>created</code> with an empty <code>domains</code>.
Before sending or receiving any payments using Diem IDs, the Treasury Compliance account must send
a transaction that invokes <code>add_domain_id</code> to set the <code>domains</code> field with a valid domain


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_publish_diem_id_domains">publish_diem_id_domains</a>(created: &signer)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_publish_diem_id_domains">publish_diem_id_domains</a>(
    created: &signer,
) {
    <a href="Roles.md#0x1_Roles_assert_parent_vasp_role">Roles::assert_parent_vasp_role</a>(created);
    <b>assert</b>(
        !<b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(<a href="../../../../../../move-stdlib/docs/Signer.md#0x1_Signer_address_of">Signer::address_of</a>(created)),
        <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_already_published">Errors::already_published</a>(<a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAIN">EDIEMIDDOMAIN</a>)
    );
    move_to(created, <a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a> {
        domains: <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_empty">Vector::empty</a>(),
    })
}
</code></pre>



</details>

<details>
<summary>Specification</summary>



<pre><code><b>include</b> <a href="Roles.md#0x1_Roles_AbortsIfNotParentVasp">Roles::AbortsIfNotParentVasp</a>{account: created};
<b>aborts_if</b> <a href="DiemId.md#0x1_DiemId_has_diem_id_domains">has_diem_id_domains</a>(<a href="../../../../../../move-stdlib/docs/Signer.md#0x1_Signer_spec_address_of">Signer::spec_address_of</a>(created)) <b>with</b> <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_ALREADY_PUBLISHED">Errors::ALREADY_PUBLISHED</a>;
</code></pre>



</details>

<a name="0x1_DiemId_has_diem_id_domains"></a>

## Function `has_diem_id_domains`



<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_has_diem_id_domains">has_diem_id_domains</a>(addr: address): bool
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_has_diem_id_domains">has_diem_id_domains</a>(addr: address): bool {
    <b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(addr)
}
</code></pre>



</details>

<a name="0x1_DiemId_publish_diem_id_domain_manager"></a>

## Function `publish_diem_id_domain_manager`

Publish a <code><a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a></code> resource under <code>tc_account</code> with an empty <code>diem_id_domain_events</code>.
When Treasury Compliance account sends a transaction that invokes <code>update_diem_id_domain</code>,
a <code><a href="DiemId.md#0x1_DiemId_DiemIdDomainEvent">DiemIdDomainEvent</a></code> is emitted and added to <code>diem_id_domain_events</code>.


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_publish_diem_id_domain_manager">publish_diem_id_domain_manager</a>(tc_account: &signer)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_publish_diem_id_domain_manager">publish_diem_id_domain_manager</a>(
    tc_account : &signer,
) {
    <a href="Roles.md#0x1_Roles_assert_treasury_compliance">Roles::assert_treasury_compliance</a>(tc_account);
    <b>assert</b>(
        !<b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a>&gt;(<a href="../../../../../../move-stdlib/docs/Signer.md#0x1_Signer_address_of">Signer::address_of</a>(tc_account)),
        <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_already_published">Errors::already_published</a>(<a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAINMANAGER">EDIEMIDDOMAINMANAGER</a>)
    );
    move_to(
        tc_account,
        <a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a> {
            diem_id_domain_events: <a href="../../../../../../move-stdlib/docs/Event.md#0x1_Event_new_event_handle">Event::new_event_handle</a>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomainEvent">DiemIdDomainEvent</a>&gt;(tc_account),
        }
    );
}
</code></pre>



</details>

<details>
<summary>Specification</summary>



<pre><code><b>include</b> <a href="Roles.md#0x1_Roles_AbortsIfNotTreasuryCompliance">Roles::AbortsIfNotTreasuryCompliance</a>{account: tc_account};
<b>aborts_if</b> <a href="DiemId.md#0x1_DiemId_tc_domain_manager_exists">tc_domain_manager_exists</a>() <b>with</b> <a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_ALREADY_PUBLISHED">Errors::ALREADY_PUBLISHED</a>;
</code></pre>



</details>

<a name="0x1_DiemId_update_diem_id_domain"></a>

## Function `update_diem_id_domain`

When updating DiemIdDomains, a simple duplicate domain check is done.
However, since domains are case insensitive, it is possible by error that two same domains in
different lowercase and uppercase format gets added.


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_update_diem_id_domain">update_diem_id_domain</a>(tc_account: &signer, to_update_address: address, domain: vector&lt;u8&gt;, is_remove: bool)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_update_diem_id_domain">update_diem_id_domain</a>(
    tc_account: &signer,
    to_update_address: address,
    domain: vector&lt;u8&gt;,
    is_remove: bool
) <b>acquires</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a>, <a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a> {
    <a href="Roles.md#0x1_Roles_assert_treasury_compliance">Roles::assert_treasury_compliance</a>(tc_account);
    <b>if</b> (!<b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(to_update_address)) {
        <b>abort</b>(<a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_not_published">Errors::not_published</a>(<a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAINSNOTPUBLISHED">EDIEMIDDOMAINSNOTPUBLISHED</a>))
    };
    <b>let</b> account_domains = borrow_global_mut&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(to_update_address);
    <b>let</b> diem_id_domain = <a href="DiemId.md#0x1_DiemId_create_diem_id_domain">create_diem_id_domain</a>(domain);
    <b>if</b> (is_remove) {
        <b>let</b> (has, index) = <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_index_of">Vector::index_of</a>(&account_domains.domains, &diem_id_domain);
        <b>if</b> (has) {
            <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_remove">Vector::remove</a>(&<b>mut</b> account_domains.domains, index);
        } <b>else</b> {
            <b>abort</b>(<a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_invalid_argument">Errors::invalid_argument</a>(<a href="DiemId.md#0x1_DiemId_EDOMAINNOTFOUND">EDOMAINNOTFOUND</a>))
        };
    } <b>else</b> {
        <b>if</b> (!<a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_contains">Vector::contains</a>(&account_domains.domains, &diem_id_domain)) {
            <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_push_back">Vector::push_back</a>(&<b>mut</b> account_domains.domains, <b>copy</b> diem_id_domain);
        } <b>else</b> {
            <b>abort</b>(<a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_invalid_argument">Errors::invalid_argument</a>(<a href="DiemId.md#0x1_DiemId_EDOMAINALREADYEXISTS">EDOMAINALREADYEXISTS</a>))
        }
    };

    <a href="../../../../../../move-stdlib/docs/Event.md#0x1_Event_emit_event">Event::emit_event</a>(
        &<b>mut</b> borrow_global_mut&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a>&gt;(<a href="CoreAddresses.md#0x1_CoreAddresses_TREASURY_COMPLIANCE_ADDRESS">CoreAddresses::TREASURY_COMPLIANCE_ADDRESS</a>()).diem_id_domain_events,
        <a href="DiemId.md#0x1_DiemId_DiemIdDomainEvent">DiemIdDomainEvent</a> {
            removed: is_remove,
            domain: diem_id_domain,
            address: to_update_address,
        },
    );
}
</code></pre>



</details>

<details>
<summary>Specification</summary>



<pre><code><b>include</b> <a href="Roles.md#0x1_Roles_AbortsIfNotTreasuryCompliance">Roles::AbortsIfNotTreasuryCompliance</a>{account: tc_account};
</code></pre>



</details>

<a name="0x1_DiemId_has_diem_id_domain"></a>

## Function `has_diem_id_domain`



<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_has_diem_id_domain">has_diem_id_domain</a>(addr: address, domain: vector&lt;u8&gt;): bool
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_has_diem_id_domain">has_diem_id_domain</a>(addr: address, domain: vector&lt;u8&gt;): bool <b>acquires</b> <a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a> {
    <b>if</b> (!<b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(addr)) {
        <b>abort</b>(<a href="../../../../../../move-stdlib/docs/Errors.md#0x1_Errors_not_published">Errors::not_published</a>(<a href="DiemId.md#0x1_DiemId_EDIEMIDDOMAINSNOTPUBLISHED">EDIEMIDDOMAINSNOTPUBLISHED</a>))
    };
    <b>let</b> account_domains = borrow_global&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomains">DiemIdDomains</a>&gt;(addr);
    <b>let</b> diem_id_domain = <a href="DiemId.md#0x1_DiemId_create_diem_id_domain">create_diem_id_domain</a>(domain);
    <a href="../../../../../../move-stdlib/docs/Vector.md#0x1_Vector_contains">Vector::contains</a>(&account_domains.domains, &diem_id_domain)
}
</code></pre>



</details>

<a name="0x1_DiemId_tc_domain_manager_exists"></a>

## Function `tc_domain_manager_exists`



<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_tc_domain_manager_exists">tc_domain_manager_exists</a>(): bool
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="DiemId.md#0x1_DiemId_tc_domain_manager_exists">tc_domain_manager_exists</a>(): bool {
    <b>exists</b>&lt;<a href="DiemId.md#0x1_DiemId_DiemIdDomainManager">DiemIdDomainManager</a>&gt;(<a href="CoreAddresses.md#0x1_CoreAddresses_TREASURY_COMPLIANCE_ADDRESS">CoreAddresses::TREASURY_COMPLIANCE_ADDRESS</a>())
}
</code></pre>



</details>


[//]: # ("File containing references which can be used from documentation")
[ACCESS_CONTROL]: https://github.com/diem/dip/blob/main/dips/dip-2.md
[ROLE]: https://github.com/diem/dip/blob/main/dips/dip-2.md#roles
[PERMISSION]: https://github.com/diem/dip/blob/main/dips/dip-2.md#permissions